#include <arpa/inet.h>
#include <fcntl.h>
#include <sys/poll.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>

#include <cassert>
#include <cinttypes>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>

#include <curl/curl.h>
#include <openssl/sha.h>
#include <zlib.h>

#include <algorithm>
#include <filesystem>
#include <list>
#include <unordered_map>
#include <vector>
#include <condition_variable>
#include <thread>

namespace fs = std::filesystem;

#define MAX_IO_SIZE_DEFAULT (8 * 1024 * 1024)
#if defined(SSIZE_MAX) && (SSIZE_MAX < MAX_IO_SIZE_DEFAULT)
#define MAX_IO_SIZE SSIZE_MAX
#else
#define MAX_IO_SIZE MAX_IO_SIZE_DEFAULT
#endif

#define BUFFER_SIZE 4096

#define GIT_SHA256_RAWSZ 32
#define GIT_MAX_RAWSZ GIT_SHA256_RAWSZ
#define GIT_SHA1_RAWSZ 20
#define GIT_SHA1_HEXSZ (2 * GIT_SHA1_RAWSZ)
#define maximum_signed_value_of_type(a) \
	(INTMAX_MAX >> (bitsizeof(intmax_t) - bitsizeof(a)))
#define signed_add_overflows(a, b) ((b) > maximum_signed_value_of_type(a) - (a))
#define maximum_unsigned_value_of_type(a) \
	(UINTMAX_MAX >> (bitsizeof(uintmax_t) - bitsizeof(a)))
#define unsigned_add_overflows(a, b) \
	((b) > maximum_unsigned_value_of_type(a) - (a))
#define bitsizeof(x) (CHAR_BIT * sizeof(x))
#ifdef __GNUC__
#define TYPEOF(x) (__typeof__(x))
#else
#define TYPEOF(x)
#endif

#define MSB(x, bits) ((x)&TYPEOF(x)(~0ULL << (bitsizeof(x) - (bits))))

#if defined(_MSC_VER)
#define DISABLE_DEPRECATED_WARNINGS_BEGIN \
	__pragma(warning(push)) __pragma(warning(disable : 4996))
#define DISABLE_DEPRECATED_WARNINGS_END __pragma(warning(pop))
#elif defined(__GNUC__)
#define DISABLE_DEPRECATED_WARNINGS_BEGIN \
	_Pragma("GCC diagnostic push")        \
		_Pragma("GCC diagnostic ignored \"-Wdeprecated-declarations\"")
#define DISABLE_DEPRECATED_WARNINGS_END _Pragma("GCC diagnostic pop")
#else
#define DISABLE_DEPRECATED_WARNINGS_BEGIN
#define DISABLE_DEPRECATED_WARNINGS_END
#endif

#define PACK_SIGNATURE 0x5041434b /* "PACK" */
#define PACK_VERSION 2
#define pack_version_ok(v) ((v) == htonl(2) || (v) == htonl(3))

enum object_type {
	OBJ_BAD	   = -1,
	OBJ_NONE   = 0,
	OBJ_COMMIT = 1,
	OBJ_TREE   = 2,
	OBJ_BLOB   = 3,
	OBJ_TAG	   = 4,
	/* 5 for future expansion */
	OBJ_OFS_DELTA = 6,
	OBJ_REF_DELTA = 7,
	OBJ_ANY,
	OBJ_MAX
};

enum file_type {
	INVALID	  = -1,
	REGULAR	  = 100644,
	DIRECTORY = 40000,
	SYMLINK	  = 120000,
	SUBMODULE = 160000
};

struct object_id {
	unsigned char hash[GIT_MAX_RAWSZ];
};

struct pack_idx_entry {
	struct object_id oid;
	uint32_t crc32;
	off_t offset;
};

struct object_entry {
	struct pack_idx_entry idx;
	unsigned long size;
	unsigned char hdr_size;
	// type defines the initial type of this entry before it is resolved
	enum object_type type;
	// real_type is the final resolved type of this entry if it needs to be
	// resolved
	enum object_type real_type;
	union {
		struct subobject *mini{}; // For tree types.
		struct {
			struct object_id obj_tree;
		};							  // For commit types.
		struct object_id base_object; // For ref delta types
	};
	unsigned char *content; // for blob types.
};

struct subobject {
	enum file_type mode;
	char *filename;
	struct object_id oid;
	struct subobject *next;
};

struct ref_delta {
	struct object_entry *base;
	bool is_resolved;
};

struct git_zstream {
	z_stream z;
	unsigned long avail_in;
	unsigned long avail_out;
	unsigned long total_in;
	unsigned long total_out;
	unsigned char *next_in;
	unsigned char *next_out;
};

struct pack_header {
	uint32_t hdr_signature;
	uint32_t hdr_version;
	uint32_t hdr_entries;
};

struct vtask {
	unsigned char *content;
	size_t size, cursor;
	struct vtask *next;
	static size_t total;
} *task_head = nullptr,
  /* An indicator to denote end of unexpected termination. */
	**task_fail = nullptr;

size_t vtask::total = 0;

std::mutex task_lock;
std::condition_variable task_watcher;

struct vtask_tail {
	struct vtask *prev = nullptr;
} vtail;

struct api_cb_data {
	CURL *curl = nullptr;
	long code{};
	void *user_data = nullptr;
	/*
	 * Holds reference to received message
	 */
	std::string recv;
};

unsigned long big_file_threshold = 512 * 1024 * 1024;
static unsigned char input_buffer[BUFFER_SIZE];
static unsigned int input_offset, input_len;
static off_t consumed_bytes;
static off_t max_input_size;
static uint32_t input_crc32;
static int input_fd, output_fd;
static int n_objects;
static int n_deltas;
/* Keep track of hash of all data we received from
 * the server so that we can confirm that we received
 * uncorrupted data.
 */
SHA_CTX input_ctx;

using ustring_view = std::basic_string_view<unsigned char>;
template <> struct std::hash<ustring_view> {
	constexpr static uint32_t default_offset_basis = 0x811C9DC5;
	constexpr static uint32_t prime				   = 0x01000193;
	std::size_t operator()(const ustring_view &k) const {
		size_t hash = default_offset_basis;
		for (auto &ch : k) {
			hash = (hash ^ ch) * prime;
		}
		return hash;
	}
};

using hash_map = std::unordered_map<ustring_view, struct object_entry *>;

static void *fill(unsigned int min);
static void flush();
static void use(unsigned int bytes);

static int handle_nonblock(int fd, short poll_events, int err);
ssize_t xread(int fd, void *buf, size_t len);
ssize_t write_in_full(int fd, const void *buf, size_t count);
ssize_t xwrite(int fd, const void *buf, size_t len);
void check_pipe(int err);
static std::unique_ptr<unsigned char[]>
unpack_raw_entry(struct object_entry *obj);
static std::unique_ptr<unsigned char[]>
unpack_entry_data(struct object_entry *obj);
static int is_delta_type(enum object_type type);

void subobject_init(struct object_entry *obj);
void subobject_update(struct object_entry *obj,
					  enum file_type mode,
					  const char *filename,
					  const char *h);
void subobject_finalize(struct object_entry *obj);

void vtask_update(struct vtask **head, unsigned char *content, size_t size);
struct vtask *vtask_pop(struct vtask **head);
void vtask_finalize(struct vtask **head);

enum file_type decode_mode(const char *mode_buf);

void make_hash(const char *hex, char *bytes);

void git_inflate_init(git_zstream *strm);
static void zlib_pre_call(git_zstream *s);
static void zlib_post_call(git_zstream *s);
static inline unsigned int zlib_buf_cap(unsigned long len);
static const char *zerr_to_string(int status);
int git_inflate(git_zstream *strm, int flush);
void git_inflate_end(git_zstream *strm);

static void die(const char *err, ...);
static void die_routine(const char *err, va_list params);
void die_errno(const char *fmt, ...);
static const char *fmt_with_err(char *buf, int n, const char *fmt);
static void bad_object(off_t offset, const char *format, ...);

int hash_cmp(const void *one, const void *other);
unsigned char hex_of(unsigned char c);

void print_hash(const unsigned char *hash, bool nl = true);

CURLcode get_response(CURL *curl, long *status = nullptr);
void api_die_on_error(const struct api_cb_data *api);

void sha_init(SHA_CTX *ctx) {
	DISABLE_DEPRECATED_WARNINGS_BEGIN;
	SHA1_Init(ctx);
	DISABLE_DEPRECATED_WARNINGS_END;
}

void sha_update(SHA_CTX *ctx, const void *in, size_t len) {
	DISABLE_DEPRECATED_WARNINGS_BEGIN;
	SHA1_Update(ctx, in, len);
	DISABLE_DEPRECATED_WARNINGS_END;
}

void sha_final(unsigned char *hash, SHA_CTX *ctx) {
	DISABLE_DEPRECATED_WARNINGS_BEGIN;
	SHA1_Final(hash, ctx);
	DISABLE_DEPRECATED_WARNINGS_END;
}

int format_object_header(char *str,
						 size_t size,
						 enum object_type type,
						 size_t objsize);

int wait_on_child(pid_t pid, bool poll = false);

const char *object_type_to_str(enum object_type type) {
	switch (type) {
		case OBJ_BAD:
			return "OBJ_BAD";
		case OBJ_NONE:
			return "OBJ_NONE";
		case OBJ_COMMIT:
			return "OBJ_COMMIT";
		case OBJ_TREE:
			return "OBJ_TREE";
		case OBJ_BLOB:
			return "OBJ_BLOB";
		case OBJ_TAG:
			return "OBJ_TAG";
		case OBJ_OFS_DELTA:
			return "OBJ_OFS_DELTA";
		case OBJ_REF_DELTA:
			return "OBJ_REF_DELTA";
		case OBJ_ANY:
			return "OBJ_ANY";
		case OBJ_MAX:
			return "OBJ_MAX";
	}

	return "";
}

static void *fill(unsigned int min) {
	if (min <= input_len)
		return input_buffer + input_offset;
	if (min > sizeof(input_buffer))
		die("cannot fill %d byte(s)", min);

	flush();
	do {
		ssize_t ret = xread(input_fd,
							input_buffer + input_len,
							sizeof(input_buffer) - input_len);
		if (ret <= 0) {
			if (!ret) {
				die("early EOF");
			}
			die_errno("read error on input");
		}
		input_len += ret;
	} while (input_len < min);
	return input_buffer;
}

static void use(unsigned int bytes) {
	if (bytes > input_len)
		die("used more bytes than were available");
	input_crc32 = crc32(input_crc32, input_buffer + input_offset, bytes);
	input_len -= bytes;
	input_offset += bytes;

	/* make sure off_t is sufficiently large not to wrap */
	if (signed_add_overflows(consumed_bytes, bytes))
		die("pack too large for current definition of off_t");
	consumed_bytes += bytes;
	if (max_input_size && consumed_bytes > max_input_size) {
		die("pack exceeds maximum allowed size (%s)", max_input_size);
	}
}

ssize_t xread(int fd, void *buf, size_t len) {
	ssize_t nr;
	if (len > MAX_IO_SIZE)
		len = MAX_IO_SIZE;
	while (true) {
		nr = read(fd, buf, len);
		if (nr < 0) {
			if (errno == EINTR)
				continue;
			if (handle_nonblock(fd, POLLIN, errno))
				continue;
		}
		return nr;
	}
}

static int handle_nonblock(int fd, short poll_events, int err) {
	struct pollfd pfd {};

	if (err != EAGAIN && err != EWOULDBLOCK)
		return 0;

	pfd.fd	   = fd;
	pfd.events = poll_events;

	/*
	 * no need to check for errors, here;
	 * a subsequent read/write will detect unrecoverable errors
	 */
	poll(&pfd, 1, -1);
	return 1;
}

static void flush() {
	if (input_offset) {
		sha_update(&input_ctx, input_buffer, input_offset);
		memmove(input_buffer, input_buffer + input_offset, input_len);
		input_offset = 0;
	}
}

ssize_t write_in_full(int fd, const void *buf, size_t count) {
	const char *p = static_cast<const char *>(buf);
	ssize_t total = 0;

	while (count > 0) {
		ssize_t written = xwrite(fd, p, count);
		if (written < 0)
			return -1;
		if (!written) {
			errno = ENOSPC;
			return -1;
		}
		count -= written;
		p += written;
		total += written;
	}

	return total;
}

ssize_t xwrite(int fd, const void *buf, size_t len) {
	ssize_t nr;
	if (len > MAX_IO_SIZE)
		len = MAX_IO_SIZE;
	while (true) {
		nr = write(fd, buf, len);
		if (nr < 0) {
			if (errno == EINTR)
				continue;
			if (handle_nonblock(fd, POLLOUT, errno))
				continue;
		}

		return nr;
	}
}

static void parse_pack_header() {
	auto *hdr =
		static_cast<struct pack_header *>(fill(sizeof(struct pack_header)));

	/* Header consistency check */
	if (hdr->hdr_signature != htonl(PACK_SIGNATURE))
		die("pack signature mismatch");
	if (!pack_version_ok(hdr->hdr_version))
		die("pack version %" PRIu32 " unsupported", ntohl(hdr->hdr_version));

	n_objects = static_cast<int>(ntohl(hdr->hdr_entries));
	printf("Number of objects: %d\n", n_objects);

	use(sizeof(struct pack_header));
}

void write_commit_tree(struct object_entry *obj_commit) {
	assert(obj_commit->real_type == OBJ_COMMIT);
	char *buf		 = reinterpret_cast<char *>(obj_commit->content), *p;
	const char *tree = "tree ";
	if ((p = strstr(buf, tree))) {
		p += strlen(tree);
		make_hash(p, reinterpret_cast<char *>(obj_commit->obj_tree.hash));
	}
}

void write_subtree(struct object_entry *obj_tree) {
	assert(obj_tree->real_type == OBJ_TREE);
	char *buf = (char *)(obj_tree->content);
	subobject_init(obj_tree);
	for (size_t j = 0; j < obj_tree->size;) {
		int hash_off = static_cast<int>(strlen(buf)) + 1;
		int shift	 = hash_off + GIT_SHA1_RAWSZ;
		subobject_update(
			obj_tree, decode_mode(buf), strchr(buf, ' ') + 1, buf + hash_off);
		buf += shift;
		j += shift;
	}
}

static std::unique_ptr<struct object_entry[]>
parse_pack_objects(struct ref_delta **refs, hash_map &obj_map) {
	unsigned char computed_hash[GIT_SHA1_RAWSZ];
	auto objects = std::make_unique<struct object_entry[]>(n_objects);

	sha_init(&input_ctx);
	for (int i = 0; i < n_objects; i++) {
		auto obj	   = &objects[i];
		auto data	   = unpack_raw_entry(obj);
		obj->real_type = obj->type;
		obj->content   = data.release();
		printf("IDX: %d, type: %s, size: %ld, hash: ",
			   i,
			   object_type_to_str(obj->real_type),
			   obj->size);
		print_hash(is_delta_type(obj->real_type) ? obj->base_object.hash :
												   obj->idx.oid.hash);
		if (obj->type == OBJ_REF_DELTA) {
			++n_deltas;
		} else if (obj->type == OBJ_TREE) {
			write_subtree(obj);
		} else if (obj->type == OBJ_COMMIT) {
			write_commit_tree(obj);
		}
	}

	flush();

	sha_final(computed_hash, &input_ctx);
	if (hash_cmp(fill(GIT_SHA1_RAWSZ), computed_hash)) {
		close(input_fd);
		die("pack is corrupted (SHA1 mismatch)");
	}

	use(GIT_SHA1_RAWSZ);

	auto objs = objects.get();
	if (n_deltas > 0) {
		*refs = new ref_delta[n_deltas];
	}
	printf("Number of refs: %d\n", n_deltas);

	for (int i = 0, j = 0; i < n_objects; ++i) {
		if (is_delta_type(objs[i].type)) {
			(*refs)[j++] = { .base = &objs[i], .is_resolved = false };
		} else {
			auto hash	  = ustring_view(objs[i].idx.oid.hash, GIT_SHA1_RAWSZ);
			obj_map[hash] = &objs[i];
		}
	}

	return objects;
}

static std::unique_ptr<unsigned char[]>
unpack_raw_entry(struct object_entry *obj) {
	unsigned char *p;
	unsigned long size, c;
	unsigned shift;

	obj->idx.offset = consumed_bytes;
	input_crc32		= crc32(0, nullptr, 0);

	p = static_cast<unsigned char *>(fill(1));
	c = *p;
	use(1);
	obj->type = static_cast<enum object_type>((c >> 4) & 7);
	size	  = (c & 15);
	shift	  = 4;
	while (c & 0x80) {
		p = static_cast<unsigned char *>(fill(1));
		c = *p;
		use(1);
		size += (c & 0x7f) << shift;
		shift += 7;
	}
	obj->size = size;

	switch (obj->type) {
		case OBJ_REF_DELTA:
			memcpy(
				&obj->base_object.hash, fill(GIT_SHA1_RAWSZ), GIT_SHA1_RAWSZ);
			use(GIT_SHA1_RAWSZ);
			break;
		case OBJ_OFS_DELTA:
			assert(0);
			die("Encountered unsupported delta (%s) type",
				object_type_to_str(obj->type));
			break;
		case OBJ_COMMIT:
		case OBJ_TREE:
		case OBJ_BLOB:
		case OBJ_TAG:
			break;
		default:
			die("unknown object type %d", obj->type);
	}
	obj->hdr_size = consumed_bytes - obj->idx.offset;
	printf("header size: %d\n", obj->hdr_size);
	return unpack_entry_data(obj);
}

static std::unique_ptr<unsigned char[]>
unpack_entry_data(struct object_entry *obj) {
	int status;
	git_zstream stream{};
	SHA_CTX ctx;
	std::unique_ptr<unsigned char[]> buf;
	char hdr[GIT_MAX_RAWSZ];
	int hdrlen;
	enum object_type type = obj->type;
	size_t size			  = obj->size;
	off_t offset		  = obj->idx.offset;

	bool is_not_delta_type = !is_delta_type(type);

	if (is_not_delta_type) {
		hdrlen = format_object_header(hdr, sizeof(hdr), type, size);
		sha_init(&ctx);
		sha_update(&ctx, hdr, hdrlen);
	}

	buf.reset(new unsigned char[size]);

	memset(&stream, 0, sizeof(stream));
	git_inflate_init(&stream);
	stream.next_out	 = static_cast<unsigned char *>(buf.get());
	stream.avail_out = size;

	do {
		unsigned char *last_out = stream.next_out;
		stream.next_in			= static_cast<unsigned char *>(fill(1));
		stream.avail_in			= input_len;
		status					= git_inflate(&stream, 0);
		use(input_len - stream.avail_in);
		if (is_not_delta_type) {
			sha_update(&ctx, last_out, stream.next_out - last_out);
		}
	} while (status == Z_OK);
	if (stream.total_out != size || status != Z_STREAM_END)
		bad_object(offset, "inflate returned %d", status);
	git_inflate_end(&stream);

	if (is_not_delta_type) {
		sha_final(obj->idx.oid.hash, &ctx);
	}

	obj->idx.crc32 = input_crc32;
	printf("crc32: %u\n", input_crc32);

	return buf;
}

static inline unsigned long get_delta_hdr_size(const unsigned char **datap,
											   const unsigned char *top) {
	const unsigned char *data = *datap;
	size_t cmd, size = 0;
	int i = 0;
	do {
		cmd = *data++;
		size |= (cmd & 0x7f) << i;
		i += 7;
	} while (cmd & 0x80 && data < top);
	*datap = data;
	return static_cast<unsigned long>(size);
}

/* the smallest possible delta size is 4 bytes */
#define DELTA_SIZE_MIN 4
std::unique_ptr<unsigned char> patch_delta(const void *src_buf,
										   unsigned long src_size,
										   const void *delta_buf,
										   unsigned long delta_size,
										   unsigned long *dst_size) {
	const unsigned char *data, *top;
	unsigned char *out, cmd;
	unsigned long size;
	std::unique_ptr<unsigned char> dst_buf;

	if (delta_size < DELTA_SIZE_MIN)
		return nullptr;

	data = static_cast<const unsigned char *>(delta_buf);
	top	 = static_cast<const unsigned char *>(delta_buf) + delta_size;

	/* make sure the orig file size matches what we expect */
	size = get_delta_hdr_size(&data, top);
	if (size != src_size)
		return nullptr;

	/* now the result size */
	size = get_delta_hdr_size(&data, top);
	dst_buf.reset(new unsigned char[size]);

	out = dst_buf.get();
	while (data < top) {
		cmd = *data++;
		if (cmd & 0x80) {
			unsigned long cp_off = 0, cp_size = 0;
#define PARSE_CP_PARAM(bit, var, shift)                       \
	do {                                                      \
		if (cmd & (bit)) {                                    \
			if (data >= top)                                  \
				die("Error occurred while processing delta"); \
			var |= ((unsigned)*data++ << (shift));            \
		}                                                     \
	} while (0)
			PARSE_CP_PARAM(0x01, cp_off, 0);
			PARSE_CP_PARAM(0x02, cp_off, 8);
			PARSE_CP_PARAM(0x04, cp_off, 16);
			PARSE_CP_PARAM(0x08, cp_off, 24);
			PARSE_CP_PARAM(0x10, cp_size, 0);
			PARSE_CP_PARAM(0x20, cp_size, 8);
			PARSE_CP_PARAM(0x40, cp_size, 16);
#undef PARSE_CP_PARAM
			if (cp_size == 0)
				cp_size = 0x10000;
			if (unsigned_add_overflows(cp_off, cp_size) ||
				cp_off + cp_size > src_size || cp_size > size)
				die("Error occurred while processing delta");
			memcpy(out, (char *)src_buf + cp_off, cp_size);
			out += cp_size;
			size -= cp_size;
		} else if (cmd) {
			if (cmd > size || cmd > top - data)
				die("Error occurred while processing delta");
			memcpy(out, data, cmd);
			out += cmd;
			data += cmd;
			size -= cmd;
		} else {
			die("unexpected delta opcode 0");
			return nullptr;
		}
	}

	/* sanity check */
	if (data != top || size != 0) {
		die("Error occurred while processing data");
		return nullptr;
	}

	*dst_size = out - dst_buf.get();
	return dst_buf;
}

void resolve_delta(struct object_entry *delta_obj, struct object_entry *base) {
	std::unique_ptr<unsigned char> result_data;
	unsigned long result_size;
	SHA_CTX ctx;
	char hdr[GIT_MAX_RAWSZ];

	result_data = patch_delta(base->content,
							  base->size,
							  delta_obj->content,
							  delta_obj->size,
							  &result_size);
	if (!result_data)
		bad_object(delta_obj->idx.offset, "failed to apply delta\n");

	delete[] delta_obj->content;

	delta_obj->content	 = result_data.release();
	delta_obj->size		 = result_size;
	delta_obj->real_type = base->real_type;
	int hdrlen			 = format_object_header(
		  hdr, sizeof(hdr), delta_obj->real_type, delta_obj->size);
	sha_init(&ctx);
	sha_update(&ctx, hdr, hdrlen);
	sha_update(&ctx, delta_obj->content, delta_obj->size);
	sha_final(delta_obj->idx.oid.hash, &ctx);

	if (delta_obj->real_type == OBJ_COMMIT) {
		write_commit_tree(delta_obj);
	} else if (delta_obj->real_type == OBJ_TREE) {
		write_subtree(delta_obj);
	}
}

void fixup_delta(struct ref_delta *refs, hash_map &obj_map) {
	for (int n_resolved = 0; n_resolved < n_deltas;) {
		ustring_view hash;
		for (int i = 0; i < n_deltas; ++i) {
			if (refs[i].is_resolved) {
				continue;
			}

			auto *ref	  = refs[i].base;
			hash		  = ustring_view(ref->base_object.hash, GIT_SHA1_RAWSZ);
			auto base_pos = obj_map.find(hash);
			if (base_pos == obj_map.end()) {
				continue;
			}

			auto *base = base_pos->second;
			resolve_delta(ref, base);
			hash			  = ustring_view(ref->idx.oid.hash, GIT_SHA1_RAWSZ);
			obj_map[hash]	  = ref;
			refs->is_resolved = true;
			++n_resolved;
		}
	}

	printf("Done!\n");
}

void subobject_init(struct object_entry *obj) {
	memset(&obj->mini, 0, sizeof(obj->mini));
}

void subobject_update(struct object_entry *obj,
					  enum file_type mode,
					  const char *filename,
					  const char *h) {
	auto *p = obj->mini;
	for (; p && p->next; p = p->next)
		;
	(p ? p->next : obj->mini) = new subobject{ .mode	 = mode,
											   .filename = strdup(filename),
											   .next	 = nullptr };
	auto *hash				  = (p ? p->next : obj->mini)->oid.hash;
	memcpy(hash, h, GIT_SHA1_RAWSZ);
}

void subobject_finalize(struct object_entry *obj) {
	if (obj->real_type == OBJ_TREE) {
		for (auto p = obj->mini; p;) {
			auto next = p->next;
			free(p->filename);
			delete p;
			p = next;
		}
	}
}

enum file_type decode_mode(const char *mo) {
	constexpr int mask = 1000;

	size_t value = 0;
	for (; mo && *mo && *mo >= '0' && *mo <= '9'; ++mo)
		value = value * 10 + *mo - '0';

	// Remove the permission bit from parsed value.
	if (value / mask == mask / 10) {
		return REGULAR;
	}
	switch (value) {
		case DIRECTORY:
			return DIRECTORY;
		case SYMLINK:
			return SYMLINK;
		case SUBMODULE:
			return SUBMODULE;
		default:
			die("Found an unsupported file type: %zu\n", value);
	}

	return INVALID;
}

static int is_delta_type(enum object_type type) {
	return (type == OBJ_REF_DELTA || type == OBJ_OFS_DELTA);
}

static const char *object_type_strings[] = {
	nullptr,  /* OBJ_NONE = 0 */
	"commit", /* OBJ_COMMIT = 1 */
	"tree",	  /* OBJ_TREE = 2 */
	"blob",	  /* OBJ_BLOB = 3 */
	"tag",	  /* OBJ_TAG = 4 */
};

const char *type_name(unsigned int type) {
	if (type >= sizeof(object_type_strings) / sizeof(object_type_strings[0]))
		return nullptr;
	return object_type_strings[type];
}

int format_object_header(char *str,
						 size_t size,
						 enum object_type type,
						 size_t objsize) {
	const char *name = type_name(type);
	return snprintf(str, size, "%s %" PRIuMAX, name, (uintmax_t)objsize) + 1;
}

void git_inflate_init(git_zstream *strm) {
	int status;

	zlib_pre_call(strm);
	status = inflateInit(&strm->z);
	zlib_post_call(strm);
	if (status == Z_OK)
		return;
	die("inflateInit: %s (%s)",
		zerr_to_string(status),
		strm->z.msg ? strm->z.msg : "no message");
}

int git_inflate(git_zstream *strm, int flush) {
	int status;

	for (;;) {
		zlib_pre_call(strm);
		/* Never say Z_FINISH unless we are feeding everything
		 */
		status =
			inflate(&strm->z, (strm->z.avail_in != strm->avail_in) ? 0 : flush);
		if (status == Z_MEM_ERROR)
			die("inflate: out of memory");
		zlib_post_call(strm);

		/*
		 * Let zlib work another round, while we can still
		 * make progress.
		 */
		if ((strm->avail_out && !strm->z.avail_out) &&
			(status == Z_OK || status == Z_BUF_ERROR))
			continue;
		break;
	}

	switch (status) {
		/* Z_BUF_ERROR: normal, needs more space in the output
		 * buffer */
		case Z_BUF_ERROR:
		case Z_OK:
		case Z_STREAM_END:
			return status;
		default:
			break;
	}
	die("inflate: %s (%s)",
		zerr_to_string(status),
		strm->z.msg ? strm->z.msg : "no message");
	return status;
}

static const char *zerr_to_string(int status) {
	switch (status) {
		case Z_MEM_ERROR:
			return "out of memory";
		case Z_VERSION_ERROR:
			return "wrong version";
		case Z_NEED_DICT:
			return "needs dictionary";
		case Z_DATA_ERROR:
			return "data stream error";
		case Z_STREAM_ERROR:
			return "stream consistency error";
		default:
			return "unknown error";
	}
}

static void zlib_pre_call(git_zstream *s) {
	s->z.next_in   = s->next_in;
	s->z.next_out  = s->next_out;
	s->z.total_in  = s->total_in;
	s->z.total_out = s->total_out;
	s->z.avail_in  = zlib_buf_cap(s->avail_in);
	s->z.avail_out = zlib_buf_cap(s->avail_out);
}

static void zlib_post_call(git_zstream *s) {
	unsigned long bytes_consumed;
	unsigned long bytes_produced;

	bytes_consumed = s->z.next_in - s->next_in;
	bytes_produced = s->z.next_out - s->next_out;
	if (s->z.total_out != s->total_out + bytes_produced)
		die("total_out mismatch");
	if (s->z.total_in != s->total_in + bytes_consumed)
		die("total_in mismatch");

	s->total_out = s->z.total_out;
	s->total_in	 = s->z.total_in;
	s->next_in	 = s->z.next_in;
	s->next_out	 = s->z.next_out;
	s->avail_in -= bytes_consumed;
	s->avail_out -= bytes_produced;
}

void git_inflate_end(git_zstream *strm) {
	int status;

	zlib_pre_call(strm);
	status = inflateEnd(&strm->z);
	zlib_post_call(strm);
	if (status == Z_OK)
		return;
	die("inflateEnd: %s (%s)",
		zerr_to_string(status),
		strm->z.msg ? strm->z.msg : "no message");
}

#define ZLIB_BUF_MAX ((uInt)1024 * 1024 * 1024) /* 1GB */
static inline unsigned int zlib_buf_cap(unsigned long len) {
	return (ZLIB_BUF_MAX < len) ? ZLIB_BUF_MAX : len;
}

static void die(const char *err, ...) {
	va_list params;

	va_start(params, err);
	die_routine(err, params);
	va_end(params);
}

static void die_routine(const char *err, va_list params) {
	vprintf(err, params);
	exit(EXIT_FAILURE);
}

void die_errno(const char *fmt, ...) {
	char buf[1024];
	va_list params;

	va_start(params, fmt);
	die_routine(fmt_with_err(buf, sizeof(buf), fmt), params);
	va_end(params);
}

static const char *fmt_with_err(char *buf, int n, const char *fmt) {
	char str_error[256], *err;
	size_t i, j;

	err = strerror(errno);
	for (i = j = 0; err[i] && j < sizeof(str_error) - 1;) {
		if ((str_error[j++] = err[i++]) != '%')
			continue;
		if (j < sizeof(str_error) - 1) {
			str_error[j++] = '%';
		} else {
			/* No room to double the '%', so we overwrite it
			 * with
			 * '\0' below */
			j--;
			break;
		}
	}
	str_error[j] = 0;
	/* Truncation is acceptable here */
	snprintf(buf, n, "%s: %s", fmt, str_error);
	return buf;
}
__attribute__((format(printf, 2, 3))) static void
bad_object(off_t offset, const char *format, ...) {
	va_list params;
	char buf[1024];

	va_start(params, format);
	vsnprintf(buf, sizeof(buf), format, params);
	va_end(params);
	die("pack has bad object at offset %" PRIuMAX ": %s",
		(uintmax_t)offset,
		buf);
}

int to_int(std::string_view ref, size_t *off) {
	int weight = 0;
	for (size_t len = ref.size(); *off < len && std::isxdigit(ref[*off]);
		 ++(*off)) {
		int code = std::tolower(ref[*off]);
		weight	 = weight * 10 + hex_of(code);
	}

	return weight;
}

std::string decode_pkt_mode(const std::string &line) {
	int band = line[0] & 0xff;
	switch (band) {
		case 3:
			die("remote error: %s", &line[1]);
			break;
		case 2:
		case 1:
			return line.substr(1);
			break;
		default:
			die("Invalid packet band received: %d, str: %s\n",
				band,
				line.data());
	}

	die("ERROR! Band %d, line %s", band, &line[0]);

	return {};
}

std::string
strm_pkt_line(std::istream &strm, bool *eof, bool should_skip = false) {
	std::string status(4, '0');

	strm.read(&status[0], status.size());
	size_t ilength = std::stoi(status, nullptr, 16);
	if (ilength <= 2) {
		*eof = true;
		return {};
	}

	std::string line(ilength - 4, 0);
	strm.read(&line[0], line.size());

	if (should_skip)
		return line;

	return decode_pkt_mode(line);
}

size_t total_size(const struct vtask *head) {
	size_t n_bytes = 0;
	for (; head; head = head->next) {
		n_bytes += head->size - head->cursor;
	}

	return n_bytes;
}

size_t read_from_head(void *buf, size_t len) {

	std::unique_lock lock(task_lock);
	task_watcher.wait(lock, [&] {
		return task_fail != nullptr ||
			   (task_head != nullptr && vtask::total >= len);
	});

	// The fetching thread exited unexpectedly.
	if (task_fail) {
		die("Unable to complete request\n");
	}

	assert(total_size(task_head) == vtask::total);

	size_t offset = 0;
	for (; task_head && offset < len;) {
		if ((task_head->size - task_head->cursor) > (len - offset)) {
			memcpy(static_cast<unsigned char *>(buf) + offset,
				   task_head->content + task_head->cursor,
				   len - offset);
			task_head->cursor += len - offset;
			vtask::total -= len - offset;
			offset += len - offset;
		} else {
			memcpy(static_cast<unsigned char *>(buf) + offset,
				   task_head->content + task_head->cursor,
				   task_head->size - task_head->cursor);
			vtask::total -= task_head->size - task_head->cursor;
			offset += task_head->size - task_head->cursor;
			auto *head = vtask_pop(&task_head);

			delete[] head->content;
			delete head;
		}
	}

	printf("total: %zu, task_head: %p\n", vtask::total, task_head);

	assert(total_size(task_head) == vtask::total);
	assert(offset == len);

	return offset;
}

std::string pkt_line_from_head(int *code, bool should_skip = false) {
	std::string status(4, '0');

	read_from_head(&status[0], status.size());
	size_t ilength = std::stoi(status, nullptr, 16);

	if (ilength <= 2) {
		*code = ilength;
		return {};
	} else {
		*code = -1;
	}

	assert(ilength > 0);
	std::string line(ilength - 4, 0);
	read_from_head(&line[0], line.size());

	if (should_skip)
		return line;

	return decode_pkt_mode(line);
}

int hash_cmp(const void *one, const void *other) {
	auto status = memcmp(one, other, GIT_SHA1_RAWSZ);
	return std::clamp(status, -1, 1);
}

void print_hash(const unsigned char *hash, bool nl) {
	for (int j = 0; j < GIT_SHA1_RAWSZ; ++j) {
		printf("%02x", hash[j]);
	}
	if (nl) {
		putchar('\n');
	}
}

struct object_entry *find_object(const hash_map &obj_map,
								 struct object_id oid) {
	auto hash = ustring_view(oid.hash, GIT_SHA1_RAWSZ);
	auto pos  = obj_map.find(hash);
	return pos == obj_map.end() ? nullptr : pos->second;
}

unsigned char hex_of(unsigned char c) {
	assert(std::isxdigit(c));
	int v = c >= '0' && c <= '9' ?
				c - '0' :
				(c >= 'a' && c <= 'f' ? c - 'a' : c - 'A') + 10;
	return v;
}

int correct_mode(int mode) {
	mode %= 10000;
	int oct	  = 0;
	int scale = 1;
	while (mode) {
		oct += (mode % 10) * scale;
		scale *= 8;
		mode /= 10;
	}
	return oct;
}

void make_hash(const char *hex, char *bytes) {
	for (int i = 0; i < GIT_SHA1_RAWSZ; ++i) {
		bytes[i] = hex_of(hex[i * 2]) << 4 | hex_of(hex[i * 2 + 1]);
	}
}

bool is_basic_file_type(int mode) {
	return mode != SYMLINK && mode != SUBMODULE;
}

void create_structure(const hash_map &obj_map,
					  struct object_entry *tree,
					  const fs::path &basedir) {
	for (auto *p = tree->mini; p; p = p->next) {
		auto filepath = basedir / p->filename;
		printf("%d %s\n", p->mode, filepath.c_str());
		if (p->mode == DIRECTORY) {
			auto *o = find_object(obj_map, p->oid);
			assert(o && o->real_type == OBJ_TREE);
			fs::create_directory(filepath);
			create_structure(obj_map, o, filepath);
		} else if (is_basic_file_type(p->mode)) {
			auto *o = find_object(obj_map, p->oid);
			assert(o);
			assert(o->real_type == OBJ_BLOB);
			auto fd = open(filepath.c_str(),
						   O_WRONLY | O_CREAT | O_TRUNC,
						   correct_mode(p->mode));
			if (fd < 0) {
				die_errno("open failed");
			} else {
				write_in_full(fd, o->content, o->size);
				close(fd);
			}
		}
	}
}

void make_tree(std::string_view url, std::string_view commit_hash) {
	struct ref_delta *refs = nullptr;
	hash_map obj_map;
	parse_pack_header();
	auto base	  = parse_pack_objects(&refs, obj_map);
	auto *objects = base.get();
	fixup_delta(refs, obj_map);

	struct object_id root {};
	make_hash(commit_hash.data(), reinterpret_cast<char *>(root.hash));
	struct object_entry *o = find_object(obj_map, root);
	if (!o) {
		die("Invalid commit hash provided %s\n", commit_hash.data());
	}

	assert(o->real_type == OBJ_COMMIT);
	struct object_entry *tree = find_object(obj_map, o->obj_tree);
	assert(tree && tree->real_type == OBJ_TREE);

	std::string dirname = fs::path(url).stem();
	if (fs::exists(dirname)) {
		fs::remove_all(dirname);
	}
	fs::create_directory(dirname);
	create_structure(obj_map, tree, dirname);

	for (int i = 0; i < n_objects; ++i) {
		auto obj = objects[i];
		subobject_finalize(&obj);
		delete[] obj.content;
	}

	if (refs) {
		delete[] refs;
	}
}

static int trace_curl(CURL *handle,
					  curl_infotype type,
					  char *data,
					  size_t size,
					  void *clientp) {
#ifdef TRACE_CURL
	(void)handle; /* prevent compiler warning */
	(void)clientp;

	switch (type) {
		case CURLINFO_TEXT:
			fputs("== Info: ", stdout);
			fwrite(data, size, 1, stdout);
		default: /* in case a new one is introduced to shock us */
			return 0;

		case CURLINFO_HEADER_OUT:
			printf("=> Send header ");
			fwrite(data, size, 1, stdout);
			break;
		case CURLINFO_DATA_OUT:
			printf("=> Send data ");
			fwrite(data, size, 1, stdout);
			putchar('\n');
			break;
		case CURLINFO_SSL_DATA_OUT:
			break;
		case CURLINFO_HEADER_IN:
			printf("<= Recv header ");
			fwrite(data, size, 1, stdout);
			break;
		case CURLINFO_DATA_IN:
			printf("<= Recv data ");
			fwrite(data, size, 1, stdout);
			putchar('\n');
			break;
		case CURLINFO_SSL_DATA_IN:
			break;
	}
#else
	(void)handle;
	(void)type;
	(void)clientp;
	(void)data;
	(void)size;

#endif

	// dump(text, stderr, (unsigned char *)data, size);
	return 0;
}

struct curl_slist *add_generic_headers(struct curl_slist *list) {
	list = curl_slist_append(list,
							 "Content-Type: "
							 "application/x-git-upload-pack-request");
	list = curl_slist_append(list,
							 "Accept: "
							 "application/x-git-upload-pack-result");
	list = curl_slist_append(list,
							 "Accept-Language: "
							 "en-Us, *;q=0.9");
	list = curl_slist_append(list,
							 "Pragma: "
							 "no-cache");
	list = curl_slist_append(list, "Expect:");
	list = curl_slist_append(list,
							 "Git-Protocol: "
							 "version=2");
	return list;
}

void set_abort_condition(CURL *curl) {
	/* abort if slower than 30 bytes/sec during 60 seconds */
	curl_easy_setopt(curl, CURLOPT_LOW_SPEED_TIME, 30L);
	curl_easy_setopt(curl, CURLOPT_LOW_SPEED_LIMIT, 60L);
}

std::string add_query_params(std::string_view url,
							 std::string_view query_param) {
	std::string s;
	const char *ext = ".git";
	size_t ext_len	= strlen(ext);
	size_t endpos	= url.size() - ext_len;
	size_t i		= 0;
	for (; i < ext_len && url[endpos + i] == ext[i]; ++i)
		;

	s.append(url);
	if (i == 0) {
		s.append(ext);
	}
	s.append("/");
	s.append(query_param);

	return s;
}

void vtask_update(struct vtask **head, unsigned char *content, size_t size) {
	auto *dup = new unsigned char[size];
	memcpy(dup, content, size);
	auto *task =
		new vtask{ .content = dup, .size = size, .cursor = 0, .next = nullptr };
	if (*head) {
		vtail.prev->next = task;
		vtail.prev		 = vtail.prev->next;
	} else {
		(*head)	   = task;
		vtail.prev = (*head);
	}
}

struct vtask *vtask_pop(struct vtask **head) {
	assert(*head);
	auto *next = (*head)->next;
	auto *task = (*head);
	(*head)	   = next;

	return task;
}

void vtask_finalize(struct vtask **head) {
	for (auto *p = *head; p;) {
		auto *next = p->next;
		delete[] p->content;
		delete p;

		p = next;
	}
	vtail.prev = nullptr;
}

struct check_pktline_state {
	char len_buf[4];
	int len_filled;
	int remaining;
};

static void
check_pktline(struct check_pktline_state *state, const char *ptr, size_t size) {
	while (size) {
		if (!state->remaining) {
			int digits_remaining = 4 - state->len_filled;
			if (digits_remaining > static_cast<int>(size))
				digits_remaining = size;
			memcpy(&state->len_buf[state->len_filled], ptr, digits_remaining);
			state->len_filled += digits_remaining;
			ptr += digits_remaining;
			size -= digits_remaining;

			if (state->len_filled == 4) {
				state->remaining = std::stoi(state->len_buf, nullptr, 16);
				if (state->remaining < 0) {
					die("remote-curl: bad line length character: %.4s",
						state->len_buf);
				} else if (state->remaining == 2) {
					die("remote-curl: unexpected response end packet");
				} else if (state->remaining < 4) {
					state->remaining = 0;
				} else {
					state->remaining -= 4;
				}
				state->len_filled = 0;
			}
		}

		if (state->remaining) {
			int remaining = state->remaining;
			if (remaining > static_cast<int>(size))
				remaining = size;
			ptr += remaining;
			size -= remaining;
			state->remaining -= remaining;
		}
	}
}

size_t
forward_response_cb(void *content, size_t size, size_t nmemb, void *raw) {
	auto *api	= static_cast<struct api_cb_data *>(raw);
	auto *state = static_cast<struct check_pktline_state *>(api->user_data);

	if (get_response(api->curl, &api->code) != CURLE_OK) {
		return size * nmemb;
	}

	if (api->code >= 300) {
		api->recv = static_cast<char *>(content);
		return size * nmemb;
	}

	check_pktline(state, static_cast<const char *>(content), size * nmemb);
	{
		std::lock_guard _(task_lock);
		vtask::total += size * nmemb;
		vtask_update(
			&task_head, static_cast<unsigned char *>(content), size * nmemb);
	}
	task_watcher.notify_all();

	return size * nmemb;
}

struct fetch_args {
	const char *hash;
	const char *url;
};

void *fetch_package(void *param) {
	auto *pck				 = static_cast<struct fetch_args *>(param);
	std::string commit_hash	 = pck->hash;
	const char *original_url = pck->url;

	struct check_pktline_state check_pack;
	memset(&check_pack, 0, sizeof(check_pack));

	CURL *curl				= curl_easy_init();
	struct curl_slist *list = nullptr;
	api_cb_data api			= { .curl = curl, .user_data = &check_pack };

	auto url	 = add_query_params(original_url, "git-upload-pack");
	auto request = "0011command=fetch"
				   "0010agent=polley"
				   "0016object-format=sha10001"
				   "000dthin-pack"
				   "000cdeepen 1"
				   "0032want " +
				   commit_hash + "\n0032want " + commit_hash +
				   "\n"
				   "0010no-progress\n"
				   "0009done\n0000";

	printf("\nUrl: %s\n", url.data());

	curl_easy_setopt(curl, CURLOPT_URL, url.data());
	curl_easy_setopt(curl, CURLOPT_POST, 1L);
	curl_easy_setopt(curl, CURLOPT_POSTFIELDS, request.data());
	set_abort_condition(curl);

	list = add_generic_headers(list);
	curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);
	curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
	curl_easy_setopt(curl, CURLOPT_DEBUGFUNCTION, trace_curl);

	/* the DEBUGFUNCTION has no effect until we enable VERBOSE */
	// curl_easy_setopt(curl, CURLOPT_VERBOSE, 1L);

	curl_easy_setopt(curl, CURLOPT_WRITEDATA, &api);
	curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, forward_response_cb);

	api.code = curl_easy_perform(curl);

	curl_slist_free_all(list);
	curl_easy_cleanup(curl);

	api_die_on_error(&api);

	return nullptr;
}

pthread_t run_async(void *(*cb)(void *), void *args) {
	pthread_t thread_id;
	pthread_create(&thread_id, nullptr, cb, args);

	return thread_id;
}

pthread_t fetch_packfile_async(struct fetch_args *p) {
	return run_async(fetch_package, p);
}

void *build_tree(void *p) {
	auto *args = static_cast<struct fetch_args *>(p);
	make_tree(args->url, args->hash);
	return nullptr;
}

pthread_t build_tree_async(struct fetch_args *p) {
	return run_async(build_tree, p);
}

void read_shallow_info() {
	int code;
	do {
		pkt_line_from_head(&code, true);
	} while (code != 1 && code != 0);

	assert(code != 0);
}

void run_task(std::string_view u, std::string_view commit_hash) {
	int child_comm_fds[2]; // This pipe is used in communicating
	// with child process
	if (pipe(child_comm_fds) == -1) {
		die_errno("pipe");
	} else {
		output_fd = child_comm_fds[1];
		input_fd  = child_comm_fds[0];
	}

	pid_t cpid = fork();
	if (cpid == -1) {
		die_errno("fork");
	}

	if (cpid == 0) {
		close(output_fd);
		make_tree(u, commit_hash);
		close(input_fd);
		exit(EXIT_SUCCESS);
	} else {
		close(child_comm_fds[0]);

		struct fetch_args curl_comm = {
			.hash = commit_hash.data(),
			.url  = u.data(),
		};

		pthread_t curl_comm_id = fetch_packfile_async(&curl_comm);

		read_shallow_info();

		int code	   = -1;
		bool seen_pack = false;
		int lineno	   = 0;
		while (code != 0) {
			auto str = pkt_line_from_head(&code, ++lineno == 1);
			if (code >= 0 && code <= 2) {
				continue;
			}
			if (lineno == 1) {
				assert(str.find("packfile") != std::string::npos);
			} else if (str.find("PACK") != std::string::npos) {
				seen_pack = true;
				write_in_full(output_fd, &str[0], str.length());
			} else if (seen_pack) {
				write_in_full(output_fd, &str[0], str.length());
			}

			if (wait_on_child(-1, false) == cpid) {
				pthread_kill(curl_comm_id, SIGKILL);
				die("An error occurred while processing!\n");
			}
		}

		pthread_join(curl_comm_id, nullptr);
		wait_on_child(cpid);
		close(output_fd);
		close(input_fd);

		exit(EXIT_SUCCESS);
	}
}

size_t
query_commit_hash_cb(void *content, size_t size, size_t nmemb, void *raw) {
	std::stringstream stream;
	stream.write(static_cast<char *>(content), size * nmemb);

	auto *api  = static_cast<api_cb_data *>(raw);
	auto *hash = static_cast<char *>(api->user_data);

	if (get_response(api->curl, &api->code) != CURLE_OK) {
		return size * nmemb;
	}

	if (api->code >= 300) {
		api->recv = static_cast<char *>(content);
		return size * nmemb;
	}

	std::string commit_hash;
	bool eof = false;
	do {
		auto line = strm_pkt_line(stream, &eof, true);
		if (line.find("HEAD") != std::string::npos) {
			commit_hash = line.substr(0, GIT_SHA1_HEXSZ);
			break;
		}
	} while (stream.good() && !eof);

	if (commit_hash.empty()) {
		die("Unable to fetch commit hash");
	}

	memcpy(hash, commit_hash.data(), GIT_SHA1_HEXSZ);
	hash[GIT_SHA1_HEXSZ] = 0;

	return size * nmemb;
}

std::string query_commit_hash(std::string_view u) {
	CURL *curl = curl_easy_init();

	char hash[GIT_SHA1_HEXSZ + 1];
	if (curl) {
		struct api_cb_data api	= { .curl = curl, .user_data = hash };
		struct curl_slist *list = nullptr;
		auto url				= add_query_params(u, "git-upload-pack");
		auto request			= std::string("0014command=ls-refs\n"
											  "0010agent=polley"
											  "0016object-format=sha1"
											  "0001"
											  "0014ref-prefix HEAD\n"
											  "0000");

		printf("Url: %s\n", url.data());

		curl_easy_setopt(curl, CURLOPT_NOBODY, 0);
		curl_easy_setopt(curl, CURLOPT_URL, url.data());
		curl_easy_setopt(curl, CURLOPT_POST, 1L);
		curl_easy_setopt(curl, CURLOPT_POSTFIELDS, request.data());
		curl_easy_setopt(
			curl, CURLOPT_POSTFIELDSIZE_LARGE, curl_off_t(request.size()));
		curl_easy_setopt(curl, CURLOPT_FAILONERROR, 0);
		set_abort_condition(curl);

		list = add_generic_headers(list);
		curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);
		curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
		curl_easy_setopt(curl, CURLOPT_DEBUGFUNCTION, trace_curl);

		/* the DEBUGFUNCTION has no effect until we enable VERBOSE */
		curl_easy_setopt(curl, CURLOPT_VERBOSE, 1L);

		curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, query_commit_hash_cb);
		curl_easy_setopt(curl, CURLOPT_WRITEDATA, &api);

		api.code = curl_easy_perform(curl);

		curl_slist_free_all(list);

		api_die_on_error(&api);
	}

	curl_easy_cleanup(curl);

	printf("Read hash: %s\n", hash);

	return hash;
}

void api_die_on_error(const struct api_cb_data *api) {
	if (api->code != CURLE_OK || !api->recv.empty()) {
		{
			std::lock_guard _(task_lock);
			task_fail = &task_head;
		}
		task_watcher.notify_all();
		if (api->code != CURLE_OK) {
			die("ERROR: %s\n",
				curl_easy_strerror(static_cast<CURLcode>(api->code)));
		} else {
			die("ERROR: %s\n", api->recv.data());
		}
	}
}

size_t server_support_cb(void *contents, size_t size, size_t nmemb, void *raw) {
	auto *api = static_cast<api_cb_data *>(raw);

	if (get_response(api->curl, &api->code) != CURLE_OK) {
		return size * nmemb;
	}
	if (api->code >= 300) {
		api->recv = static_cast<char *>(contents);
		return size * nmemb;
	}

	std::stringstream stream;
	stream.write(static_cast<char *>(contents),
				 static_cast<std::streamsize>(size * nmemb));
	bool eof = false;
	do {
		auto line	= strm_pkt_line(stream, &eof, true);
		auto eq_pos = line.find('=');
		if (eq_pos != std::string::npos) {
			if (line.substr(0, eq_pos) == "object-format") {
				auto fmt = line.substr(eq_pos + 1, line.size() - eq_pos);
				if (fmt.find("sha1") == std::string::npos) {
					die("Unsupported format seen: %s, %zu\n",
						fmt.data(),
						fmt.size());
				}
			}
		}

		eof = eof && !stream.good();
		// We might encounter the delimiter but that doesn't
		// mean we are done.
	} while (stream.good() && !eof);

	return size * nmemb;
}

void query_server_support(const char *u) {
	CURL *curl = curl_easy_init();

	if (curl) {
		struct curl_slist *list = nullptr;
		auto url = add_query_params(u, "info/refs?service=git-upload-pack");
		struct api_cb_data api = { .curl = curl };

		printf("Url: %s\n", url.data());

		curl_easy_setopt(curl, CURLOPT_URL, url.data());
		set_abort_condition(curl);

		list = add_generic_headers(list);
		curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);
		curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
		curl_easy_setopt(curl, CURLOPT_DEBUGFUNCTION, trace_curl);

		/* the DEBUGFUNCTION has no effect until we enable VERBOSE */
		curl_easy_setopt(curl, CURLOPT_VERBOSE, 1L);
		curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, server_support_cb);
		curl_easy_setopt(curl, CURLOPT_WRITEDATA, &api);

		api.code = curl_easy_perform(curl);
		curl_slist_free_all(list);

		api_die_on_error(&api);
	}

	curl_easy_cleanup(curl);
}

CURLcode get_response(CURL *curl, long *status) {
	long status_code;
	long *status_p = status ? status : &status_code;
	auto code	   = curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, status_p);

	return code;
}

int main(int argc, char **argv) {
	if (argc != 2) {
		auto last_slash = strrchr(argv[0], '/');
		die("Usage: %s <git remote url>",
			last_slash ? last_slash + 1 : argv[0]);
	}

	const char *url = argv[1];
	curl_global_init(CURL_GLOBAL_ALL);
	query_server_support(url);
	std::string head = query_commit_hash(url);
	run_task(url, head);
	curl_global_cleanup();

	exit(EXIT_SUCCESS);
}

int wait_on_child(pid_t pid, bool poll) {
	int wstatus;
	int id;
	do {
		id = waitpid(pid, &wstatus, (!poll ? WNOHANG : 0) | WUNTRACED);
		if (id == -1) {
			die_errno("waitpid");
		}

		if (id > 0) {
			if (WIFEXITED(wstatus)) {
				printf("exited, status=%d\n", WEXITSTATUS(wstatus));
			} else if (WIFSIGNALED(wstatus)) {
				printf("killed by signal %d\n", WTERMSIG(wstatus));
			} else if (WIFSTOPPED(wstatus)) {
				printf("stopped by signal %d\n", WSTOPSIG(wstatus));
			} else if (WIFCONTINUED(wstatus)) {
				printf("continued\n");
			}
		}
	} while (poll && !WIFEXITED(wstatus) && !WIFSIGNALED(wstatus));

	return id;
}

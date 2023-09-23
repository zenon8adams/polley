#include <arpa/inet.h>
#include <cassert>
#include <cinttypes>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <openssl/sha.h>
#include <sys/poll.h>
#include <sys/wait.h>
#include <zlib.h>
#include <filesystem>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <curl/curl.h>

namespace fs = std::filesystem;

#ifndef MAX_IO_SIZE
#define MAX_IO_SIZE_DEFAULT (8 * 1024 * 1024)
#if defined(SSIZE_MAX) && (SSIZE_MAX < MAX_IO_SIZE_DEFAULT)
#define MAX_IO_SIZE SSIZE_MAX
#else
#define MAX_IO_SIZE MAX_IO_SIZE_DEFAULT
#endif
#endif

#define GIT_SHA256_RAWSZ 32
#define GIT_MAX_RAWSZ GIT_SHA256_RAWSZ
#define GIT_SHA1_RAWSZ 20
#define GIT_SHA1_HEXSZ (2 * GIT_SHA1_RAWSZ)
#define maximum_signed_value_of_type(a) \
	(INTMAX_MAX >> (bitsizeof(intmax_t) - bitsizeof(a)))
#define signed_add_overflows(a, b) ((b) > maximum_signed_value_of_type(a) - (a))
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
#define DISABLE_DEPRECATED_WARNINGS_BEGIN       \
	_Pragma("GCC diagnostic push") _Pragma( \
		"GCC diagnostic ignored \"-Wdeprecated-declarations\"")
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
	INVALID	   = -1,
	NORMAL	   = 100644,
	EXECUTABLE = 100755,
	DIRECTORY  = 40000,
	SYMLINK	   = 120000
};

struct object_id {
	unsigned char hash[GIT_MAX_RAWSZ];
	int algo; /* XXX requires 4-byte alignment */
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
	signed char type;
	signed char real_type;
	union {
		struct subobject *others; // For tree types.
		struct {
			struct object_id obj_tree;
			struct object_id obj_parent;
		};	       // For commit types.
		char *content; // for blob types.
	};
};

struct subobject {
	enum file_type mode;
	char *filename;
	struct object_id oid;
	struct subobject *next;
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

unsigned long big_file_threshold = 512 * 1024 * 1024;
static unsigned char input_buffer[4096];
static unsigned int input_offset, input_len;
static off_t consumed_bytes;
static off_t max_input_size;
static unsigned deepest_delta;
static uint32_t input_crc32;
static int input_fd, output_fd;
static int nr_objects;

static void *fill(unsigned int min);
static void flush(void);
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
void subobject_update(struct object_entry *obj, enum file_type mode,
		      const char *filename, const char *h);
void subobject_finalize(struct object_entry *obj);

enum file_type decode_mode(const char *mode_buf);

static inline unsigned int hexval(int c);
void hash_to_bytes(char *binary, const char *hex, size_t len);
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
void write_or_die(int fd, const void *buf, size_t count);

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

int format_object_header(char *str, size_t size, enum object_type type,
			 size_t objsize);

void wait_on_child(pid_t pid);

const char *object_type_to_str(int type) {
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
		ssize_t ret = xread(input_fd, input_buffer + input_len,
				    sizeof(input_buffer) - input_len);
		if (ret <= 0) {
			if (!ret)
				die("early EOF");
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
	while (1) {
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
	struct pollfd pfd;

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

static void flush(void) {
	if (input_offset) {
		memmove(input_buffer, input_buffer + input_offset, input_len);
		input_offset = 0;
	}
}

void write_or_die(int fd, const void *buf, size_t count) {
	if (write_in_full(fd, buf, count) < 0) {
		check_pipe(errno);
		die_errno("write error");
	}
}

void check_pipe(int err) {
	if (err == EPIPE) {
		/* Should never happen, but just in case... */
		exit(141);
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
	while (1) {
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

static void parse_pack_header(void) {
	struct pack_header *hdr = static_cast<struct pack_header *>(
		fill(sizeof(struct pack_header)));

	/* Header consistency check */
	if (hdr->hdr_signature != htonl(PACK_SIGNATURE))
		die("pack signature mismatch");
	if (!pack_version_ok(hdr->hdr_version))
		die("pack version %" PRIu32 " unsupported",
		    ntohl(hdr->hdr_version));

	nr_objects = ntohl(hdr->hdr_entries);
	printf("Number of objects: %d\n", nr_objects);

	use(sizeof(struct pack_header));
}

static std::unique_ptr<struct object_entry[]> parse_pack_objects() {
	int i;
	auto objects = std::make_unique<struct object_entry[]>(nr_objects);
	for (i = 0; i < nr_objects; i++) {
		auto obj  = &objects[i];
		auto data = unpack_raw_entry(obj);
		printf("IDX: %d, TYPE: %s HASH: ", i,
		       object_type_to_str(obj->type));
		if (!is_delta_type(static_cast<enum object_type>(obj->type))) {
			for (int j = 0; j < GIT_SHA1_RAWSZ; ++j) {
				printf("%02x", obj->idx.oid.hash[j]);
			}
			putchar(' ');
		}
		if (obj->type == OBJ_COMMIT) {
			fwrite(data.get(), 1, obj->size, stdout);
		}
		obj->real_type = obj->type;
		if (obj->type == OBJ_TREE) {
			putchar('\n');
			char *buf = (char *)(data.get());
			subobject_init(obj);
			for (size_t j = 0; j < obj->size;) {
				printf("\n%s ", (char *)buf);
				int hash_off = strlen(buf) + 1;
				for (int k = 0; k < GIT_SHA1_RAWSZ; ++k) {
					unsigned char ch = buf[hash_off + k];
					printf("%02x", ch);
				}
				int shift = hash_off + GIT_SHA1_RAWSZ;
				subobject_update(obj, decode_mode(buf),
						 strchr(buf, ' ') + 1,
						 buf + hash_off);
				buf += shift;
				j += shift;
			}
			putchar('\n');
		}

		if (obj->type == OBJ_OFS_DELTA || obj->type == OBJ_REF_DELTA) {
			;
		} else if (!data) {
			die("Error occurred while processing request");
		} else if (obj->type == OBJ_BLOB) {
			obj->content = reinterpret_cast<char *>(data.release());
		} else if (obj->type == OBJ_COMMIT) {
			char *buf	 = (char *)data.get(), *p;
			const char *tree = "tree ";
			if ((p = strstr(buf, tree))) {
				p += strlen(tree);
				make_hash(p, reinterpret_cast<char *>(
						     obj->obj_tree.hash));
			}

			const char *parent = "parent ";
			if ((p = static_cast<char *>(
				     memmem(static_cast<const void *>(buf),
					    GIT_SHA1_HEXSZ * 4, // Don't search
								// more than
								// this
					    static_cast<const void *>(parent),
					    strlen(parent))))) {
				p += strlen(parent);
				make_hash(p, reinterpret_cast<char *>(
						     obj->obj_parent.hash));
			}
		}
	}

	return objects;
}

static std::unique_ptr<unsigned char[]>
unpack_raw_entry(struct object_entry *obj) {
	unsigned char *p;
	unsigned long size, c;
	unsigned shift;
	off_t base_offset;
	struct object_id base_object;

	obj->idx.offset = consumed_bytes;
	printf("\nOffset: %zu, current crc32: %u, input_offset: %d\n",
	       consumed_bytes, input_crc32, input_buffer[input_offset]);
	input_crc32 = crc32(0, NULL, 0);

	p = static_cast<unsigned char *>(fill(1));
	c = *p;
	use(1);
	obj->type = (c >> 4) & 7;
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
	printf("Obj->Size: %ld\n", size);

	switch (obj->type) {
		case OBJ_REF_DELTA:
			memcpy(base_object.hash, fill(GIT_SHA1_RAWSZ),
			       GIT_SHA1_RAWSZ);
			use(GIT_SHA1_RAWSZ);
			printf("This %s references: ",
			       object_type_to_str(obj->type));
			for (int i = 0; i < GIT_SHA1_RAWSZ; ++i) {
				printf("%02x", base_object.hash[i]);
			}
			putchar('\n');
			break;
		case OBJ_OFS_DELTA:
			p = static_cast<unsigned char *>(fill(1));
			c = *p;
			use(1);
			base_offset = c & 127;
			while (c & 128) {
				base_offset += 1;
				if (!base_offset || MSB(base_offset, 7))
					bad_object(
						obj->idx.offset,
						"offset value overflow for delta base object");
				p = static_cast<unsigned char *>(fill(1));
				c = *p;
				use(1);
				base_offset = (base_offset << 7) + (c & 127);
			}
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
	git_zstream stream;
	SHA_CTX ctx;
	std::unique_ptr<unsigned char[]> buf;
	char hdr[32];
	int hdrlen;
	enum object_type type = static_cast<enum object_type>(obj->type);
	size_t size	      = obj->size;
	off_t offset	      = obj->idx.offset;

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
		stream.next_in		= static_cast<unsigned char *>(fill(1));
		stream.avail_in		= input_len;
		status			= git_inflate(&stream, 0);
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

void subobject_init(struct object_entry *obj) {
	memset(&obj->others, 0, sizeof(obj->others));
}

void subobject_update(struct object_entry *obj, enum file_type mode,
		      const char *filename, const char *h) {
	auto *p = obj->others;
	for (; p && p->next; p = p->next)
		;
	(p ? p->next : obj->others) = new subobject{
		.mode = mode, .filename = strdup(filename), .next = nullptr
	};
	auto *hash = (p ? p->next : obj->others)->oid.hash;
	memcpy(hash, h, GIT_SHA1_RAWSZ);
}

void subobject_finalize(struct object_entry *obj) {
	if (obj->type == OBJ_TREE) {
		for (auto p = obj->others; p;) {
			auto next = p->next;
			free(p->filename);
			delete p;
			p = next;
		}
	}
}

enum file_type decode_mode(const char *mo) {
	size_t value = 0;
	for (; mo && *mo && *mo >= '0' && *mo <= '9'; ++mo)
		value = value * 10 + *mo - '0';
	switch (value) {
		case NORMAL:
			return NORMAL;
		case EXECUTABLE:
			return EXECUTABLE;
		case DIRECTORY:
			return DIRECTORY;
		case SYMLINK:
			return SYMLINK;
		default:
			die("Found an unsupported file type: %zu\n", value);
	}

	return INVALID;
}

static int is_delta_type(enum object_type type) {
	return (type == OBJ_REF_DELTA || type == OBJ_OFS_DELTA);
}

static const char *object_type_strings[] = {
	NULL,	  /* OBJ_NONE = 0 */
	"commit", /* OBJ_COMMIT = 1 */
	"tree",	  /* OBJ_TREE = 2 */
	"blob",	  /* OBJ_BLOB = 3 */
	"tag",	  /* OBJ_TAG = 4 */
};

const char *type_name(unsigned int type) {
	if (type >=
	    sizeof(object_type_strings) / sizeof(object_type_strings[0]))
		return NULL;
	return object_type_strings[type];
}

int format_object_header(char *str, size_t size, enum object_type type,
			 size_t objsize) {
	const char *name = type_name(type);
	return snprintf(str, size, "%s %" PRIuMAX, name, (uintmax_t)objsize) +
	       1;
}

const char hexval_table[17] = "0123456789abcdef";

void hash_to_bytes(char *binary, const char *hex, size_t len) {
	for (size_t i = 0; i < len; ++i) {
		char ch		  = hex[i];
		binary[i * 2]	  = hexval((ch >> 4) & 0x0f);
		binary[i * 2 + 1] = hexval(ch & 0x0f);
	}
	binary[len * 2] = 0;
}

static inline unsigned int hexval(int c) {
	assert(c >= 0 && c <= 16);
	return hexval_table[c];
}

void git_inflate_init(git_zstream *strm) {
	int status;

	zlib_pre_call(strm);
	status = inflateInit(&strm->z);
	zlib_post_call(strm);
	if (status == Z_OK)
		return;
	die("inflateInit: %s (%s)", zerr_to_string(status),
	    strm->z.msg ? strm->z.msg : "no message");
}

int git_inflate(git_zstream *strm, int flush) {
	int status;

	for (;;) {
		zlib_pre_call(strm);
		/* Never say Z_FINISH unless we are feeding everything */
		status = inflate(&strm->z,
				 (strm->z.avail_in != strm->avail_in) ? 0 :
									flush);
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
		/* Z_BUF_ERROR: normal, needs more space in the output buffer */
		case Z_BUF_ERROR:
		case Z_OK:
		case Z_STREAM_END:
			return status;
		default:
			break;
	}
	die("inflate: %s (%s)", zerr_to_string(status),
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
	s->total_in  = s->z.total_in;
	s->next_in   = s->z.next_in;
	s->next_out  = s->z.next_out;
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
	die("inflateEnd: %s (%s)", zerr_to_string(status),
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
			/* No room to double the '%', so we overwrite it with
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
	die("pack has bad object at offset %" PRIuMAX ": %s", (uintmax_t)offset,
	    buf);
}

template <typename Stream>
std::string strm_pkt_line(Stream &&strm, bool *eof, bool should_skip = false) {
	std::string status(4, '0');

	if constexpr (std::is_integral_v<std::remove_reference_t<Stream>>) {
		read(strm, &status[0], status.size());
	} else {
		strm.read(&status[0], status.size());
	}
	if (status == "0000" || status == "0001" || status == "0002") {
		*eof = true;
		return {};
	}

	size_t ilength = std::stoi(status, nullptr, 16);
	std::string line(ilength - 4, 0);
	if constexpr (std::is_integral_v<std::decay_t<Stream>>) {
		read(strm, &line[0], line.size());
	} else {
		strm.read(&line[0], line.size());
	}
	if (should_skip)
		return line;

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
			die("Invalid packet band received: %d", band);
	}

	die("ERROR! Band %d, line %s", band, &line[0]);

	return {};
}

int hash_cmp(const void *one, const void *other) {
	return memcmp(
		static_cast<const struct object_entry *>(one)->idx.oid.hash,
		static_cast<const struct object_entry *>(other)->idx.oid.hash,
		GIT_SHA1_RAWSZ);
}

int obj_entry_hash_cmp(const void *key, const void *other) {
	return memcmp(
		static_cast<const struct object_id *>(key)->hash,
		static_cast<const struct object_entry *>(other)->idx.oid.hash,
		GIT_SHA1_RAWSZ);
}

struct object_entry *find_object(struct object_entry *objects,
				 struct object_id oid) {
	return static_cast<struct object_entry *>(
		bsearch(&oid, objects, nr_objects, sizeof(*objects), hash_cmp));
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

void create_structure(struct object_entry *objects, struct object_entry *tree,
		      fs::path basedir) {
	for (auto *p = tree->others; p; p = p->next) {
		auto filepath = basedir / p->filename;
		printf("%d %s\n", p->mode, filepath.c_str());
		if (p->mode == DIRECTORY) {
			auto *o = find_object(objects, p->oid);
			assert(o->type == OBJ_TREE);
			fs::create_directory(filepath);
			create_structure(objects, o, filepath);
		} else if (p->mode != SYMLINK) {
			printf("hash: ");
			for (int i = 0; i < GIT_SHA1_RAWSZ; ++i)
				printf("%02x", p->oid.hash[i]);
			putchar('\n');
			auto *o = find_object(objects, p->oid);
			assert(o);
			printf("Object type: %s\n",
			       object_type_to_str(o->type));
			assert(o->type == OBJ_BLOB);
			auto fd = open(filepath.c_str(),
				       O_WRONLY | O_CREAT | O_TRUNC,
				       correct_mode(p->mode));
			if (fd < 0) {
				die_errno("open failed");
			} else {
				write_in_full(fd, o->content, o->size);
			}
		}
	}
}

void make_tree(std::string_view url, std::string_view commit_hash) {
	parse_pack_header();
	auto base     = parse_pack_objects();
	auto *objects = base.get();
	qsort(objects, nr_objects, sizeof(*objects), hash_cmp);

	struct object_id root;
	make_hash(commit_hash.data(), reinterpret_cast<char *>(root.hash));
	struct object_entry *o = nullptr, *tree = nullptr;
	while ((o = find_object(objects, root))) {
		assert(o->type == OBJ_COMMIT);
		tree = find_object(objects, o->obj_tree);
		if (tree && tree->type == OBJ_TREE) {
			break;
		}
		memcpy(root.hash, o->obj_parent.hash, GIT_SHA1_RAWSZ);
	}
	if (!o) {
		die("Invalid commit hash provided %s\n", commit_hash.data());
	}

	printf("\nroot hash: ");
	for (int i = 0; i < GIT_SHA1_RAWSZ; ++i) {
		printf("%02x", root.hash[i]);
	}
	printf(", tree hash: ");
	for (int i = 0; i < GIT_SHA1_RAWSZ; ++i) {
		printf("%02x", tree->idx.oid.hash[i]);
	}
	putchar('\n');

	std::string dirname = fs::path(url).stem();
	if (fs::exists(dirname)) {
		fs::remove_all(dirname);
	}
	fs::create_directory(dirname);
	create_structure(objects, tree, dirname);

	for (int i = 0; i < nr_objects; ++i) {
		auto obj = objects[i];
		subobject_finalize(&obj);
		if (obj.type == OBJ_BLOB) {
			delete[] obj.content;
		}
	}
}

struct curl_slist *add_generic_headers(struct curl_slist *list) {
	list = curl_slist_append(list, "Content-Type: "
				       "application/x-gitupload-pack-request");
	list = curl_slist_append(list, "Accept: "
				       "application/x-gitupload-pack-result");
	list = curl_slist_append(list, "Accept-Language: "
				       "en-Us, *;q=0.9");
	list = curl_slist_append(list, "Pragma: "
				       "no-cache");
	list = curl_slist_append(list, "Git-Protocol: "
				       "version=2");
	return list;
}

std::string add_query_params(std::string_view url,
			     std::string_view query_param) {
	std::string s;
	const char *ext = ".git";
	size_t ext_len	= strlen(ext);
	size_t endpos	= url.size() - ext_len;
	size_t i	= 0;
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

size_t forward_response_cb(void *contents, size_t size, size_t nmemb,
			   void *fd) {
	return write(*static_cast<int *>(fd), contents, size * nmemb);
}

struct fetch_args {
	const char *hash;
	const char *url;
	int comm_fd;
};

void *fetch_package(void *param) {
	struct fetch_args *pck	 = static_cast<struct fetch_args *>(param);
	std::string commit_hash	 = pck->hash;
	const char *original_url = pck->url;
	int comm_fd		 = pck->comm_fd;

	char tmp_file[] = "fetch_XXXXXX";
	int fd		= mkostemp(tmp_file, O_RDWR);
	if (fd < 0) {
		die_errno("mkostemp");
	}

	CURL *curl		= curl_easy_init();
	struct curl_slist *list = nullptr;

	auto url     = add_query_params(original_url, "git-upload-pack");
	auto request = "0011command=fetch"
		       "000fagent=fetch"
		       "0016object-format=sha10001"
		       "000dthin-pack"
		       "0032want " +
		       commit_hash + "\n0032want " + commit_hash +
		       "\n0009done\n0000";

	printf("Url: %s\n", url.data());

	curl_easy_setopt(curl, CURLOPT_URL, url.data());
	curl_easy_setopt(curl, CURLOPT_POST, 1L);
	curl_easy_setopt(curl, CURLOPT_WRITEDATA, &fd);
	curl_easy_setopt(curl, CURLOPT_POSTFIELDS, request.data());

	list = add_generic_headers(list);
	curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);

	curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, forward_response_cb);

	curl_easy_perform(curl);

	char buf[4096];
	size_t count = 0;

	printf("Done!\n");
	lseek(fd, SEEK_SET, 0);
	while ((count = xread(fd, buf, sizeof(buf)))) {
		write_in_full(comm_fd, buf, count);
	}

	unlink(tmp_file);
	curl_slist_free_all(list);
	curl_easy_cleanup(curl);

	return nullptr;
}

pthread_t fetch_packfile_async(struct fetch_args *p) {
	pthread_t thread_id;
	pthread_create(&thread_id, nullptr, fetch_package, p);

	return thread_id;
}

void query_packfile(std::string_view u, std::string_view commit_hash) {
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
	} else {
		// Setup pipe to communicate with curl callback
		int curl_comm_fds[2];
		if (pipe(curl_comm_fds) == -1) {
			die_errno("pipe");
		}
		close(child_comm_fds[0]);

		struct fetch_args curl_comm = {
			.hash	 = commit_hash.data(),
			.url	 = u.data(),
			.comm_fd = curl_comm_fds[1],
		};

		pthread_t curl_comm_id = fetch_packfile_async(&curl_comm);

		char tmp_file[] = "pack_XXXXXX.pack";
		int fd = mkostemps(tmp_file, 5, O_WRONLY | O_CREAT | O_APPEND);
		if (fd < 0) {
			die("mkostemps");
		}

		bool eof       = false;
		bool seen_pack = false;
		int lineno     = 0;
		while (!eof) {
			auto str = strm_pkt_line(curl_comm_fds[0], &eof,
						 ++lineno == 1);
			if (lineno == 1) {
				assert(!strncmp(&str[0], "packfile", 8));
			} else if (!strncmp(&str[0], "PACK", 4)) {
				seen_pack = true;
				write_in_full(output_fd, &str[0], str.length());
				write_in_full(fd, &str[0], str.length());
			} else if (seen_pack) {
				write_in_full(output_fd, &str[0], str.length());
				write_in_full(fd, &str[0], str.length());
			}
			if (!seen_pack) {
				std::cout << str;
			}
		}

		close(output_fd);
		close(input_fd);
		pthread_join(curl_comm_id, nullptr);
		wait_on_child(cpid);
		close(curl_comm_fds[0]);
		close(curl_comm_fds[1]);
	}
}

size_t query_commit_hash_cb(void *contents, size_t size, size_t nmemb,
			    void *hash) {
	std::stringstream stream;
	stream.write(static_cast<char *>(contents), size * nmemb);

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

	memcpy(static_cast<char *>(hash), commit_hash.data(), GIT_SHA1_HEXSZ);
	static_cast<char *>(hash)[GIT_SHA1_HEXSZ] = 0;

	return size * nmemb;
}

std::string query_commit_hash(std::string_view u) {
	CURL *curl = curl_easy_init();

	char hash[GIT_SHA1_HEXSZ + 1];
	if (curl) {
		struct curl_slist *list = nullptr;
		auto url     = add_query_params(u, "git-upload-pack");
		auto request = "0014command=ls-refs\n"
			       "0016agent=git/2.41.GIT"
			       "0016object-format=sha1"
			       "0001"
			       "0009peel\n"
			       "000csymrefs\n"
			       "000bunborn\n"
			       "0014ref-prefix HEAD\n"
			       "0000";

		printf("Url: %s\n", url.data());

		curl_easy_setopt(curl, CURLOPT_URL, url.data());
		curl_easy_setopt(curl, CURLOPT_POST, 1L);
		curl_easy_setopt(curl, CURLOPT_WRITEDATA, hash);
		curl_easy_setopt(curl, CURLOPT_POSTFIELDS, request);

		list = add_generic_headers(list);
		curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);

		curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION,
				 query_commit_hash_cb);

		curl_easy_perform(curl);

		curl_slist_free_all(list);
	}

	curl_easy_cleanup(curl);

	printf("Read hash: %s\n", hash);

	return hash;
}

size_t server_support_cb(void *contents, size_t size, size_t nmemb) {
	std::stringstream stream;
	stream.write(static_cast<char *>(contents), size * nmemb);
	bool eof = false;
	do {
		auto line   = strm_pkt_line(stream, &eof, true);
		auto eq_pos = line.find('=');
		if (eq_pos != std::string::npos) {
			if (line.substr(0, eq_pos) == "object-format") {
				auto fmt = line.substr(eq_pos + 1,
						       line.size() - eq_pos);
				if (fmt.find("sha1") == std::string::npos) {
					die("Unsupported format seen: %s, %zu\n",
					    fmt.data(), fmt.size());
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
		auto url		= add_query_params(
				       u, "info/refs?service=git-upload-pack");

		printf("Url: %s\n", url.data());

		curl_easy_setopt(curl, CURLOPT_URL, url.data());
		curl_easy_setopt(curl, CURLOPT_WRITEDATA, u);

		list = add_generic_headers(list);
		curl_easy_setopt(curl, CURLOPT_HTTPHEADER, list);

		curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION,
				 server_support_cb);

		curl_easy_perform(curl);

		curl_slist_free_all(list);
	}

	curl_easy_cleanup(curl);
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
	query_packfile(url, head);
	curl_global_cleanup();
}

void wait_on_child(pid_t pid) {
	int wstatus;
	do {
		pid_t w = waitpid(pid, &wstatus, WUNTRACED | WCONTINUED);
		if (w == -1) {
			die_errno("waitpid");
		}

		if (WIFEXITED(wstatus)) {
			printf("exited, status=%d\n", WEXITSTATUS(wstatus));
		} else if (WIFSIGNALED(wstatus)) {
			printf("killed by signal %d\n", WTERMSIG(wstatus));
		} else if (WIFSTOPPED(wstatus)) {
			printf("stopped by signal %d\n", WSTOPSIG(wstatus));
		} else if (WIFCONTINUED(wstatus)) {
			printf("continued\n");
		}
	} while (!WIFEXITED(wstatus) && !WIFSIGNALED(wstatus));
}

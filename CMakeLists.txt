cmake_minimum_required(VERSION 3.10)

project(polley)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -ggdb -fstandalone-debug -fsanitize=address")

add_executable(${PROJECT_NAME} main.cpp)

include(cmake/CPM.cmake)

CPMAddPackage(NAME curl VERSION 8.3.0 GITHUB_REPOSITORY curl/curl GIT_TAG curl-8_3_0)
CPMAddPackage(NAME Zlib VERSION 1.3 GITHUB_REPOSITORY madler/zlib GIT_TAG v1.3)

target_link_libraries(${PROJECT_NAME} PUBLIC libcurl -lpthread zlib crypto)

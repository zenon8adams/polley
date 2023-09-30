cmake_minimum_required(VERSION 3.10)

project(polley)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -ggdb -fstandalone-debug")
add_executable(${PROJECT_NAME} main.cpp)
target_link_libraries(${PROJECT_NAME} PUBLIC -lcurl -lpthread -lz -lcrypto)
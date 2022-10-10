cmake_minimum_required(VERSION 3.15)

project(CASymba C)

# LTO enabled except for debug builds
include(CheckIPOSupported)
check_ipo_supported(RESULT is_ipo_supported OUTPUT lto_error)
if(is_ipo_supported)
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION_Release ON)
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION_Debug OFF)
endif()

set(GLOBAL_COMPILER_FLAGS "-W -Wall -Wextra -Werror -march=native -Wunused-function -Werror=write-strings -Werror=redundant-decls -Werror=format -Werror=format-security -Werror=implicit-function-declaration -Werror=return-type -Werror=pointer-arith -Winit-self -Wimplicit-fallthrough")
set(CMAKE_C_FLAGS   "${CMAKE_C_FLAGS} ${GLOBAL_COMPILER_FLAGS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${GLOBAL_COMPILER_FLAGS}")

set(CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} -fno-omit-frame-pointer -fsanitize=address,bounds")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -fno-omit-frame-pointer -fsanitize=address,bounds")
set(CMAKE_LINKER_FLAGS_DEBUG "${CMAKE_LINKER_FLAGS_DEBUG} -fno-omit-frame-pointer -fsanitize=address,bounds")

file(GLOB sources "src/*.[ch]*")

add_executable(CASymba ${sources})

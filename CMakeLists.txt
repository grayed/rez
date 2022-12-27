cmake_minimum_required(VERSION 3.12)
project(rez CXX)
set(CMAKE_CXX_STANDARD 20)

list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

add_executable(${CMAKE_PROJECT_NAME}
	rez.cpp
	)
install(TARGETS ${CMAKE_PROJECT_NAME} DESTINATION bin) 

if (APPLE OR CMAKE_SYSTEM_NAME MATCHES ".*BSD.*")
	message(STATUS "It looks you're running BSD system and do not need libbsd")
else()
	find_package(BSD REQUIRED)
	list(APPEND BSD_DEFINITIONS -DLIBBSD_OVERLAY)
	list(APPEND BSD_DEFINITIONS -D_BSD_SOURCE=1 -D_GNU_SOURCE=1 -D_DEFAULT_SOURCE=1 -D_XOPEN_SOURCE=700)

	# libbsd warns about OpenBSD vs. NetBSD strnvis incompatibility
	list(APPEND BSD_DEFINITIONS -Wno-error=cpp)

	add_definitions(${BSD_DEFINITIONS})
	target_include_directories(${CMAKE_PROJECT_NAME} PRIVATE ${BSD_INCLUDE_DIRS})
	target_link_libraries(${CMAKE_PROJECT_NAME} ${BSD_LIBRARIES})
	set_target_properties(${CMAKE_PROJECT_NAME} PROPERTIES
		COMPILE_OPTIONS "-include${CMAKE_CURRENT_SOURCE_DIR}/compat.h"
		)
endif()

if (CMAKE_C_COMPILER_ID STREQUAL Clang OR CMAKE_C_COMPILER_ID STREQUAL GNU)
	set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra -Wno-unused")
	set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wstrict-prototypes -Wmissing-prototypes -Wmissing-declarations")
	set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wshadow -Wpointer-arith -Wcast-qual -Wsign-compare")

	set(CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} -Werror")
endif()

# man handling
set(MANDIR "${CMAKE_INSTALL_PREFIX}/man" CACHE PATH "Prefix to directory where to install manual page")
message(STATUS "Manual page will be installed under ${MANDIR}")

install(FILES ${CMAKE_PROJECT_NAME}.1 DESTINATION "${MANDIR}/man1")

enable_testing()
add_subdirectory(tests)

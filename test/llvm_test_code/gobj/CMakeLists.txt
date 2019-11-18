set(gobj_files
  invalid-narrowing-cast.c
  invalid-narrowing-cast-1.c
  invalid-narrowing-cast-2.c
  incompatible-cast-1.c
  invalid-bitcast-1.c
  viewer-pink.c
  viewer-file.c
  viewer-green.c
)

foreach(TEST_SRC ${gobj_files})
  generate_ll_file(FILE ${TEST_SRC} DEBUG MEM2REG INCLUDE ${CMAKE_CURRENT_SOURCE_DIR})
endforeach(TEST_SRC)

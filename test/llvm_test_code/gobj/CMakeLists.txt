set(gobj_files
  invalid-narrowing-cast.c
  viewer-pink.c
  viewer-file.c
)

foreach(TEST_SRC ${gobj_files})
  generate_ll_file(FILE ${TEST_SRC} DEBUG INCLUDE ${CMAKE_CURRENT_SOURCE_DIR})
endforeach(TEST_SRC)

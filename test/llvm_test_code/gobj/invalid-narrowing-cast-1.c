#include <glib.h>

#include "viewer-file.h"
#include "viewer-pink.h"

typedef struct S {
  ViewerFile *f1;
} S;

static void allocate_file(S *s) {
  GObject *otherobj = g_object_new(VIEWER_TYPE_FILE, NULL);
  s->f1 = VIEWER_FILE(otherobj); // cast to viewer file type
}

static void allocate_pink(S *s) {
  GObject *otherobj = g_object_new(VIEWER_TYPE_PINK, NULL);
  s->f1 = VIEWER_FILE(otherobj); // cast to viewer file type
}

static void cast_to_pink(S *s) {
  ViewerFile *f = s->f1;
  ViewerPink *p = VIEWER_PINK(f);
  viewer_make_it_pink(p);
}

// Verify that types flow through pointers that are wrapped inside
// structures.
static void test_object (void)
{
  S s, t;
  // create a viewer_file object
  allocate_file(&s);
  // create a viewer_pink object
  allocate_pink(&t);
  // cast object to viewer_pink
  cast_to_pink(&s);
  cast_to_pink(&t);
}


int main() {
  test_object();
}

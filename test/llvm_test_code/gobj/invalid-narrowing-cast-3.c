#include <glib.h>

#include "viewer-file.h"
#include "viewer-pink.h"

typedef struct S {
  GObject *f1;
} S;

static void allocate_file(S *s) {
  s->f1 = g_object_new(VIEWER_TYPE_FILE, NULL);
}


static void cast_to_pink(S *s) {
  GObject *f = s->f1;
  ViewerPink *p = VIEWER_PINK(f);
  (void) p;
}

// Verify that types flow through pointers that are wrapped inside
// structures.
static void test_object (void)
{
  S s, t;
  // create a viewer_file object
  allocate_file(&s);
  // cast object to viewer_pink
  cast_to_pink(&s);
}


int main() {
  test_object();
}

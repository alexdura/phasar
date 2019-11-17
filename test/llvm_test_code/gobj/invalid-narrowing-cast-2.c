#include <glib.h>

#include "viewer-file.h"
#include "viewer-pink.h"

typedef struct S {
  GObject *g1, *g2;
} S;

static void test_object (void)
{
  S s;
  // Build a VIEWER_FILE object, but cast it to a subtype
  s.g1 = g_object_new(VIEWER_TYPE_FILE, NULL);
  ViewerFile *vf = VIEWER_FILE(s.g1); // cast to viewer file type
  viewer_file_open(vf, NULL); // this is correct
  ViewerPink *not_pink = VIEWER_PINK(vf); // this is not correct
  viewer_make_it_pink(not_pink); // this should fail
  g_object_unref(G_OBJECT (s.g1));
}

int main() {
  test_object();
}

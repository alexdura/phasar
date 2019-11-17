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
  s.g2 = g_object_new(VIEWER_TYPE_PINK, NULL);
  ViewerFile *vf = VIEWER_FILE(s.g1); // cast to viewer file type
  viewer_file_open(vf, NULL); // this is correct
  ViewerPink *not_pink = VIEWER_PINK(s.g1); // this is not correct
  viewer_make_it_pink(not_pink); // this should fail
  ViewerPink *pink = VIEWER_PINK(s.g2); // this is correct and should not be reported
  viewer_make_it_pink(pink);
  g_object_unref(G_OBJECT (s.g1));
  g_object_unref(G_OBJECT (s.g2));
}

int main() {
  test_object();
}

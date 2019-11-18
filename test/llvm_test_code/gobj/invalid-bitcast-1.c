#include <glib.h>

#include "viewer-file.h"
#include "viewer-pink.h"

static void test_object (void)
{
  // Build a VIEWER_FILE object, but cast it to a subtype
  GObject *otherobj = g_object_new(VIEWER_TYPE_FILE, NULL);
  ViewerFile *vf = (ViewerFile*)(otherobj); // cast to viewer file type
  viewer_file_open(vf, NULL); // this is correct
  ViewerPink *not_pink = (ViewerPink*)(vf); // this is not correct
  viewer_make_it_pink(not_pink); // this should fail
  g_object_unref(G_OBJECT (otherobj));
}


int main() {
  test_object();
}

#include <glib.h>
#include "viewer-pink.h"

G_DEFINE_TYPE(ViewerPink, viewer_pink, VIEWER_TYPE_FILE)

static void
viewer_pink_make_it_pink_impl(void) {
  g_print("VIEWER_PINK: made it pink\n");
}

static void
viewer_pink_open_impl(ViewerFile *self, GError **error) {
  g_print("VIEWER_PINK: Pink viewer opened\n");
}

static void
viewer_pink_class_init(ViewerPinkClass *klass) {
  klass->make_it_pink = viewer_pink_make_it_pink_impl;
  klass->open = viewer_pink_open_impl;
  g_print("Viewer pink class initialized\n");
}

static void
viewer_pink_init (ViewerPink *self) {
  g_print("Viewer pink object initialized\n");
}

void viewer_make_it_pink(ViewerPink *self) {
  ViewerPinkClass *klass = VIEWER_PINK_GET_CLASS (self);
  klass->make_it_pink();
}

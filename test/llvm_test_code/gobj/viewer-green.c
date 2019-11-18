#include <glib.h>
#include "viewer-green.h"

G_DEFINE_TYPE(ViewerGreen, viewer_green, VIEWER_TYPE_FILE)

static void
viewer_green_make_it_green_impl(void) {
  g_print("VIEWER_GREEN: made it green\n");
}

static void
viewer_green_open_impl(ViewerFile *self, GError **error) {
  g_print("VIEWER_GREEN: Green viewer opened\n");
}

static void
viewer_green_class_init(ViewerGreenClass *klass) {
  klass->make_it_green = viewer_green_make_it_green_impl;
  klass->open = viewer_green_open_impl;
  g_print("Viewer green class initialized\n");
}

static void
viewer_green_init (ViewerGreen *self) {
  g_print("Viewer green object initialized\n");
}

void viewer_make_it_green(ViewerGreen *self) {
  ViewerGreenClass *klass = VIEWER_GREEN_GET_CLASS (self);
  klass->make_it_green();
}

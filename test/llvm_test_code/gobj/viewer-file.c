#include <glib.h>
#include "viewer-file.h"

/// Viewer file stuff
// This type has to be defined by the user, its purpose is to hold private data
// for the class.
typedef struct {
  int x;
} ViewerFilePrivate;

G_DEFINE_TYPE_WITH_PRIVATE (ViewerFile, viewer_file, G_TYPE_OBJECT)

static void
viewer_file_open_impl(ViewerFile *self, GError **error) {
  g_print("VIEWER_FILE: Print file opened\n");
}

static void
viewer_file_class_init (ViewerFileClass *klass)
{
  klass->open = viewer_file_open_impl;
  g_print("Viewer file class initialized\n");
}

static void
viewer_file_init (ViewerFile *self)
{
  ViewerFilePrivate *priv = viewer_file_get_instance_private (self);

  /* initialize all public and private members to reasonable default values.
   * They are all automatically initialized to 0 to begin with. */
  g_print("Viewer file object initialized\n");
}

void viewer_file_open(ViewerFile *self, GError **error) {
  ViewerFileClass *klass;
  klass = VIEWER_FILE_GET_CLASS (self);
  klass->open(self, error);
}

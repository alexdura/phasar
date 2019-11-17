#include <glib.h>

#include "viewer-file.h"
#include "viewer-pink.h"

typedef struct S {
  ViewerFile *f1;
  ViewerFile *f2;
} S;

static void allocate_1(S *s) {
  GObject *otherobj = g_object_new(VIEWER_TYPE_FILE, NULL);
  s->f2 = VIEWER_FILE(otherobj); // cast to viewer file type
}

static void allocate_2(S *s) {
  GObject *otherobj = g_object_new(VIEWER_TYPE_PINK, NULL);
  s->f2 = VIEWER_FILE(otherobj); // cast to viewer file type
}

static void cast_to_pink(S *s, int n) {
  ViewerFile *f = n == 0 ? s->f1 : s->f2;
  ViewerPink *p = VIEWER_PINK(f);
  viewer_make_it_pink(p);
}

static void cast_to_pink_1(S *s) {
  ViewerFile *f = s->f1;
  ViewerPink *p = VIEWER_PINK(f);
  viewer_make_it_pink(p);
}

static void cast_to_pink_2(S *s) {
  ViewerFile *f = s->f2;
  ViewerPink *p = VIEWER_PINK(f);
  viewer_make_it_pink(p);
}

static void test_object (void)
{
  S s;
  allocate_1(&s);
  allocate_2(&s);

  //cast_to_pink(&s, 0);
  //cast_to_pink(&s, 1);

  cast_to_pink_1(&s);
  cast_to_pink_2(&s);
}


int main() {
  test_object();
}

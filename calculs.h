#include "simplify.h"

Tree* diff(Tree* tr, const char* vr);
Tree* diff_n(Tree* tr, const char* vr, int k);
Tree* diff_partial(Tree* tr, const char* vr, const char* vr1);
Tree* tangline(Tree* tr, const char* vr, Tree* point);
Tree* taylor(Tree* u, Tree* vr, Tree* point, Tree* ordre);
Tree* integrals_by_part(Tree* f, const char* x);
Tree* integral(Tree* tr, const char* x);
Tree* analyse(Tree* tr);
Tree* pow_transform(Tree* u);

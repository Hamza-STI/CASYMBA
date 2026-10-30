#include "includes.h"

static Tree* taylor_usuelle(Tree* u, const char* vr, Tree* ordre, Tree* point)
{
	Tree* s = simplify(remplace_tree(u, vr, point));
	if (s->tok_type == UNDEF)
	{
		clean_tree(s);
		Error = push_back_dlist(Error, err_msg[1]);
		return NULL;
	}
	Tree* dtr = clone(u);
	int n = (int)tonumber(ordre->value), i;
	for (i = 1; i <= n; i++)
	{
		Tree* diff_r = simplify(diff(dtr, vr));
		clean_tree(dtr);
		dtr = diff_r;
		char* fi = factoriel(i);
		Tree* a = join(simplify(remplace_tree(dtr, vr, point)), new_tree(fi), fnc[DIVID].ex);
		free(fi);
		Tree* b = join(simplify(join(new_tree(vr), clone(point), fnc[SUB].ex)), new_tree(tostr(i)), fnc[POW].ex);
		Tree* c = simplify(join(a, b, fnc[PROD].ex));
		if (strcmp(c->value, "0") && c->tok_type != UNDEF)
			s = (s == NULL) ? c : join(s, c, fnc[ADD].ex);
		else
			clean_tree(c);
	}
	clean_tree(dtr);
	return s;
}

static bool usuelle_forme(token a)
{
	return a == COS_F || a == SIN_F || a == LN_F || a == COSH_F || a == SINH_F || a == EXP_F || a == SQRT_F;
}

Tree* taylor(Tree* u, Tree* vr, Tree* ordre, Tree* point)
{
	token tk = u->tok_type;
	if ((tk == LN_F || tk == SQRT_F || tk == POW) && ismonomial(u->tleft, vr->value) && !strcmp(point->value, "0"))
		return clone(u);
	if (usuelle_forme(tk))
	{
		Tree* ord = clone(ordre);
		if (ispoly(u->tleft, vr->value))
		{
			Tree* dg = degree_sv(u->tleft, vr->value);
			ord = simplify(join(ord, dg, fnc[DIVID].ex));
		}
		else if (u->tleft->tok_type == SQRT_F)
			ord = simplify(join(ord, new_tree("2"), fnc[PROD].ex));
		Tree* tr = join(new_tree("XX"), NULL, u->value);
		Tree* ty = taylor_usuelle(tr, "XX", ord, point);
		clean_tree(ord); clean_tree(tr);
		tr = remplace_tree(ty, "XX", u->tleft);
		clean_tree(ty);
		return simplify(tr);
	}
	else if (tk == PROD)
	{
		Tree* v = taylor(u->tleft, vr, ordre, point), * w = taylor(u->tright, vr, ordre, point);
		if (v == NULL || w == NULL)
		{
			clean_tree(v); clean_tree(w);
			Error = push_back_dlist(Error, err_msg[1]);
			return NULL;
		}
		map lv = map_create_add(v), lw = map_create_add(w);
		clean_tree(v); clean_tree(w);
		Tree* s = new_tree("0");
		double g = Eval(ordre);
		for (Cell* tmp_v = lv->begin; tmp_v != NULL; tmp_v = tmp_v->next)
		{
			for (Cell* tmp_w = lw->begin; tmp_w != NULL; tmp_w = tmp_w->next)
			{
				Tree* d = join(degree_sv(tmp_v->data, vr->value), degree_sv(tmp_w->data, vr->value), fnc[ADD].ex);
				double h = Eval(d);
				clean_tree(d);
				if (h <= g)
					s = join(s, simplify(join(tmp_v->data, tmp_w->data, fnc[PROD].ex)), fnc[ADD].ex);
				else
					break;
			}
		}
		lv = clear_map(lv);
		lw = clear_map(lw);
		return simplify(s);
	}
	else if (tk == ADD || tk == SUB)
	{
		Tree* v = taylor(u->tleft, vr, ordre, point), * w = taylor(u->tright, vr, ordre, point);
		if (v == NULL || w == NULL)
		{
			clean_tree(v); clean_tree(w);
			Error = push_back_dlist(Error, err_msg[1]);
			return NULL;
		}
		return simplify(join(v, w, u->value));
	}
	return clone(u);
}
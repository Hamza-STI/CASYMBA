#include "simplify.h"

#define AMONT_VALUE_TRIG 15
bool ALG_EXPAND = false;
bool LN_EXP_EXPAND = false;
bool TRIG_EXPAND = false;
bool RT_SIMP = false;

static const struct Trigo_value Exact_Values[AMONT_VALUE_TRIG] =
{
	/* remarquables */
	{ "0", "1", "0", "0" },
	{ "PI/6", "sqrt(3)/2", "1/2", "sqrt(3)/3" },
	{ "PI/4", "sqrt(2)/2", "sqrt(2)/2", "1" },
	{ "PI/3", "1/2", "sqrt(3)/2", "sqrt(3)" },
	{ "PI/2", "1", "0", fnc[UNDEF].ex },
	{ "(2*PI)/3", "~1/2", "sqrt(3)/2", "~sqrt(3)" },
	{ "(3*PI)/4", "~sqrt(2)/2", "sqrt(2)/2", "~1" },
	{ "(5*PI)/6", "~sqrt(3)/2", "1/2", "~sqrt(3)/3" },
	{ "PI", "~1", "0", "0" },

	/* moins-remarquables */
	{ "PI/12", "sqrt(2+sqrt(3))/2", "sqrt(2-sqrt(3))/2", "2-sqrt(3)" },
	{ "PI/10", "sqrt(10+2*sqrt(5))/4", "(~1+sqrt(5))/4", "sqrt((5-2*sqrt(5))/5)" },
	{ "PI/8", "sqrt(2+sqrt(2))/2", "sqrt(2-sqrt(2))/2", "~1+sqrt(2)" },
	{ "PI/5", "(1+sqrt(5))/4", "sqrt(10-2*sqrt(5))/4",	"sqrt(5-2*sqrt(5))" },
	{ "(3*PI)/8", "sqrt(2-sqrt(2))/2", "sqrt(2+sqrt(2))/2", "1+sqrt(2)" },
	{ "(5*PI)/12", "sqrt(2-sqrt(3))/2", "sqrt(2+sqrt(3))/2", "2+sqrt(3)" }
};

static Tree* evaluate_add(Tree* left, Tree* right);
static Tree* evaluate_diff(Tree* left, Tree* right);
static Tree* evaluate_prod(Tree* left, Tree* right);
static Tree* simplify_RNE(Tree* u);
static Tree* simplify_RNE_rec(Tree* u);
static Tree* simplify_rational_number(Tree* u);
static Tree* evaluate_diff(Tree* left, Tree* right);
static Tree* simplify_oper(map L, token tk);
static Tree* simplify_ln(Tree* u);
static Tree* simplify_exp(Tree* u);
static map simplify_oper_rec(map L, token tk);

static Tree* construct(const char* op, map* L);
static Tree* rationalize_sum(Tree* u, Tree* v, const char* op);
static Tree* contract_exp(Tree* u);
static Tree* contract_ln_rules(Tree* u);
static Tree* contract_ln(Tree* u);
static Tree* expand_exp(Tree* u);
static Tree* expand_ln(Tree* u);

static map merge(map p, map q, token tk);
static Tree* absolute_value(Tree* u);

bool ispoly(Tree* u, const char* vr)
{
	token tk = u->tok_type;
	if (tk == NEGATIF)
		return ispoly(u->tleft, vr);
	if (u->gtype == FUNCTION)
		return !found_element(u->tleft, vr);
	if (tk == ADD || tk == SUB || tk == PROD)
		return ispoly(u->tleft, vr) && ispoly(u->tright, vr);
	if (tk == DIVID)
		return ispoly(u->tleft, vr) && !found_element(u->tright, vr);
	if (tk == POW)
		return ispoly(u->tleft, vr) && u->tright->gtype == ENT;
	return (u->gtype <= VAR);
}

bool is_int(Tree* u)
{
	if (u->tok_type == NEGATIF)
		return is_int(u->tleft);
	return (u->gtype == ENT);
}

bool isdemi(Tree* tr)
{
	return tr->tok_type == DIVID && !strcmp(tr->tleft->value, "1") && !strcmp(tr->tright->value, "2");
}

static Tree* clean_and_return(Tree* u, Tree* result)
{
	clean_tree(u);
	return result;
}

static Tree* reorder(Tree* a, Tree* c)
{
	return (ordre_tree(a, c)) ? join(a, c, fnc[PROD].ex) : join(c, a, fnc[PROD].ex);
}

Tree* pow_transform(Tree* u)
{
	if (u->tok_type == POW && (isdemi(u->tright) || !strcmp(u->tright->value, "1") || u->tright->tok_type == NEGATIF))
	{
		u->tleft = pow_transform(u->tleft);
		Tree* v = clone(u->tleft);
		if (isdemi(u->tright))
			v = join(v, NULL, fnc[SQRT_F].ex);
		else if (u->tright->tok_type == NEGATIF)
			v = join(new_tree("1"), pow_transform(join(v, clone(u->tright->tleft), fnc[POW].ex)), fnc[DIVID].ex);
		v->parent = u->parent;
		clean_tree(u);
		return v;
	}
	else if (u->gtype == OPERAT)
	{
		u->tleft = pow_transform(u->tleft);
		u->tright = pow_transform(u->tright);
		if (u->tok_type == PROD)
		{
			if (!strcmp(u->tleft->value, "1"))
				return clean_and_return(u, clone(u->tright));
			if (!strcmp(u->tright->value, "1"))
				return clean_and_return(u, clone(u->tleft));
			if (u->tleft->tok_type == DIVID && !strcmp(u->tleft->tleft->value, "1") && u->tright->tok_type != DIVID)
				return clean_and_return(u, join(clone(u->tright), clone(u->tleft->tright), fnc[DIVID].ex));
			if (u->tright->tok_type == DIVID && !strcmp(u->tright->tleft->value, "1") && u->tleft->tok_type != DIVID)
				return clean_and_return(u, join(clone(u->tleft), clone(u->tright->tright), fnc[DIVID].ex));
			if (u->tleft->tok_type == DIVID || u->tright->tok_type == DIVID)
			{
				Tree* a = numerator_fun(u->tleft), * b = denominator_fun(u->tleft);
				Tree* c = numerator_fun(u->tright), * d = denominator_fun(u->tright);
				clean_tree(u);
				a = reorder(a, c);
				bool k = !strcmp(b->value, "1");
				if (k || !strcmp(d->value, "1"))
				{
					clean_tree(k ? b : d);
					return join(a, k ? d : b, fnc[DIVID].ex);
				}
				b = reorder(b, d);
				u = join(a, b, fnc[DIVID].ex);
			}
			if (u->tleft->tok_type == NEGATIF && !strcmp(u->tleft->tleft->value, "1"))
				return clean_and_return(u, join(clone(u->tright), NULL, fnc[NEGATIF].ex));
		}
	}
	else if (u->gtype == FUNCTION || u->gtype == NEGATION)
		u->tleft = pow_transform(u->tleft);
	return u;
}

Tree* numerator_fun(Tree* u)
{
	if (u->tok_type == DIVID)
		return clone(u->tleft);
	if (u->tok_type == POW && isconstant(u->tright) && Eval(u->tright) < 0)
		return new_tree("1");
	else if (u->tok_type == NEGATIF)
		return simplify(join(numerator_fun(u->tleft), NULL, fnc[NEGATIF].ex));
	else if (u->tok_type == PROD)
		return simplify(join(numerator_fun(u->tleft), numerator_fun(u->tright), fnc[PROD].ex));
	return clone(u);
}

Tree* denominator_fun(Tree* u)
{
	if (u->tok_type == DIVID)
		return clone(u->tright);
	if (u->tok_type == POW && isconstant(u->tright) && Eval(u->tright) < 0)
		return simplify(join(clone(u), join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex));
	else if (u->tok_type == NEGATIF)
		return denominator_fun(u->tleft);
	if (u->tok_type == PROD)
		return simplify(join(denominator_fun(u->tleft), denominator_fun(u->tright), fnc[PROD].ex));
	return new_tree("1");
}

static Tree* base(Tree* u)
{
	return (u->tok_type == POW) ? u->tleft : u;
}

static Tree* exponent(Tree* u)
{
	return (u->tok_type == POW) ? clone(u->tright) : new_tree("1");
}

long long int factoriel(int a)
{
	long long int s = 1, i;
	for (i = 1; i <= a; ++i)
		s *= i;
	return s;
}

static float fpart(double ex)
{
	return (float)(ex - (int)ex);
}

static Tree* expand_product(Tree* r, Tree* s)
{
	if (r->tok_type == ADD || r->tok_type == SUB)
		return join(simplify(expand_product(r->tleft, s)), simplify(expand_product(r->tright, s)), r->value);
	else if (s->tok_type == ADD || s->tok_type == SUB)
		return expand_product(s, r);
	return join(clone(r), clone(s), fnc[PROD].ex);
}

static Tree* expand_power(Tree* u, int n)
{
	if (u->tok_type == ADD || u->tok_type == SUB)
	{
		Tree* f = u->tleft, * r = u->tright, * s = new_tree("0");
		for (int i = 0; i <= n; ++i)
		{
			Tree* g = join(clone(f), new_tree(tostr(n - i)), fnc[POW].ex);
			double c = (double)factoriel(n) / (factoriel(i) * factoriel(n - i));
			Tree* a = simplify(join(new_tree(tostr(c)), g, fnc[PROD].ex)), * b = simplify(expand_power(r, i));
			Tree* t = expand_product(a, b);
			s = join(s, t, u->value);
			clean_tree(a); clean_tree(b);
		}
		return s;
	}
	return join(clone(u), new_tree(tostr(n)), fnc[POW].ex);
}

Tree* expand(Tree* tr)
{
	token tk = tr->tok_type;
	if (tk == ADD || tk == SUB || tk == DIVID)
		return join(expand(tr->tleft), expand(tr->tright), tr->value);
	else if (tk == PROD)
	{
		Tree* tr1 = expand(tr->tleft), * tr2 = expand(tr->tright);
		Tree* t = expand_product(tr1, tr2);
		clean_tree(tr1); clean_tree(tr2);
		return t;
	}
	else if (tk == POW)
	{
		Tree* u = expand(tr->tleft), * v = tr->tright;
		if (v->gtype == ENT && (u->tok_type == ADD || u->tok_type == SUB))
		{
			int t = (int)tonumber(v->value);
			if (t >= 2 && t <= 255)
			{
				Tree* a = expand_power(u, t);
				clean_tree(u);
				return a;
			}
		}
		clean_tree(u);
	}
	else if (tk == LN_F && LN_EXP_EXPAND)
		return expand_ln(tr);
	else if (tk == EXP_F && LN_EXP_EXPAND)
		return expand_exp(tr);
	return clone(tr);
}

static Tree* expand_main_com(map* L, map* M, token tok)
{
	mapCell* tmp = (*L)->begin;
	Tree* tr = NULL;
	while (tmp != NULL)
	{
		mapCell* tmp1 = (*M)->begin;
		while (tmp1 != NULL)
		{
			Tree* w = join(clone(tmp->data), clone(tmp1->data), fnc[tok].ex);
			tr = (!tr) ? w : join(tr, w, fnc[ADD].ex);
			tmp1 = tmp1->next;
		}
		tmp = tmp->next;
	}
	*L = clear_map(*L);
	*M = clear_map(*M);
	return tr;
}

Tree* expand_main_op(Tree* u)
{
	if (u->tok_type == DIVID)
	{
		Tree* r = u->tleft;
		if (r->tok_type == ADD || r->tok_type == SUB)
		{
			map L = map_create_add(r), M = push_back_map(NULL, u->tright);
			return expand_main_com(&L, &M, DIVID);
		}
	}
	if (u->tok_type == PROD)
	{
		map L = map_create_add(u->tleft), M = map_create_add(u->tright);
		return expand_main_com(&L, &M, PROD);
	}
	if (u->tok_type == POW && u->tright->gtype == ENT && ALG_EXPAND)
	{
		int d = (int)Eval(u->tright);
		if (d <= 10)
			return expand_power(u->tleft, d);
	}
	return clone(u);
}

static bool clear_and_return(map* p, map* q, bool k)
{
	*p = clear_map(*p);
	*q = clear_map(*q);
	return k;
}

static bool ordre_tree1(Tree* u, Tree* v)
{
	map p = map_create(u), q = map_create(v);
	if (!tree_compare(p->end->data, q->end->data))
		return clear_and_return(&p, &q, ordre_tree(p->end->data, q->end->data));
	mapCell* tmp = p->end, * tmp1 = q->end;
	while (tmp != NULL && tmp1 != NULL)
	{
		if (!tree_compare(tmp->data, tmp1->data))
			return clear_and_return(&p, &q, ordre_tree(tmp->data, tmp1->data));
		tmp = tmp->back;
		tmp1 = tmp1->back;
	}
	return clear_and_return(&p, &q, p->length < q->length);
}

static bool ordre_tree2(Tree* u, Tree* v)
{
	Tree* tr = join(clone(v), new_tree("1"), fnc[POW].ex);
	bool k = !ordre_tree(tr, u);
	clean_tree(tr);
	return k;
}

bool ordre_tree(Tree* u, Tree* v)
{
	if (isconstant(u) && isconstant(v))
		return Eval(u) < Eval(v);
	if (u->gtype == VAR && v->gtype == VAR)
		return strcmp(u->value, v->value) < 0;
	if (v->gtype == FUNCTION && u->gtype == VAR)
		return 1;
	if (u->tok_type == v->tok_type && (u->tok_type == ADD || u->tok_type == PROD))
		return ordre_tree1(u, v);
	if (u->tok_type == v->tok_type && u->tok_type == POW)
	{
		Tree* p = base(u), * r = base(v);
		return (!tree_compare(p, r)) ? ordre_tree(p, r) : ordre_tree(u->tright, v->tright);
	}
	if (u->tok_type == v->tok_type && u->tok_type == FACTORIEL_F)
		return ordre_tree(u->tleft, v->tleft);
	if (u->gtype == FUNCTION && v->gtype == FUNCTION)
		return (u->tok_type != v->tok_type) ? strcmp(u->value, v->value) < 0 : ordre_tree1(u->tleft, v->tleft);
	if (isconstant(u) && !isconstant(v))
		return 1;
	if (u->tok_type == PROD && (v->tok_type == POW || v->tok_type == ADD || v->gtype == FUNCTION || v->gtype == VAR))
		return ordre_tree(u->tright, v);
	if (u->tok_type == ADD && (v->gtype == FUNCTION || v->gtype == VAR))
		return ordre_tree(u->tright, v);
	if (v->tok_type == PROD && (u->tok_type == POW || u->tok_type == ADD || u->gtype == FUNCTION || u->gtype == VAR))
		return !ordre_tree(v->tright, u);
	if (v->tok_type == ADD && (u->gtype == FUNCTION || u->gtype == VAR))
		return !ordre_tree(v->tright, u);
	if (u->tok_type == FACTORIEL_F && ((v->gtype == FUNCTION && v->tok_type != FACTORIEL_F) || v->gtype == VAR))
		return ordre_tree(u->tleft, v);
	if (u->tok_type == POW && v->tok_type != POW)
		return ordre_tree2(u, v);
	if (u->tok_type != POW && v->tok_type == POW)
		return !ordre_tree2(v, u);
	return false;
}

map map_sort(map li)
{
	mapCell* tmp = li->begin;
	while (tmp != NULL)
	{
		mapCell* tmp1 = li->begin;
		while (tmp1 != NULL)
		{
			if (ordre_tree(tmp->data, tmp1->data))
			{
				Tree* t = tmp1->data;
				tmp1->data = tmp->data;
				tmp->data = t;
			}
			tmp1 = tmp1->next;
		}
		tmp = tmp->next;
	}
	return li;
}

static Tree* trigo_identify(const char* s, token tk)
{
	for (const Trigo_value* element = Exact_Values; element != Exact_Values + AMONT_VALUE_TRIG; element++)
	{
		if ((COS_F <= tk && tk <= TAN_F) && !strcmp(s, element->angle))
			return to_tree(In2post2((tk == SIN_F) ? element->sin_value : (tk == COS_F) ? element->cos_value : element->tan_value));
		else if (!strcmp(s, element->cos_value) || !strcmp(s, element->sin_value) || !strcmp(s, element->tan_value))
			return to_tree(In2post2(element->angle));
	}
	return NULL;
}

Tree* PGCD(Tree* A, Tree* B)
{
	Tree* r = simplify(join(A, clone(B), fnc[SUB].ex));
	if (strcmp(r->value, "0"))
		return PGCD(B, simplify(join(r, NULL, fnc[ABS_F].ex)));
	clean_tree(r);
	return B;
}

/* numerical simplify */

static Tree* fracOp(Tree* numerator, Tree* denominator)
{
	if (!strcmp(numerator->value, "0"))
		return clone(numerator);
	Number num = { 1, numerator->value }, denom = { 1, denominator->value };
	if (numerator->gtype == ENT && denominator->gtype == ENT)
	{
		Number pgcd = gcd(num, denom);
		Number a = int_divid(num, pgcd, NULL), b = int_divid(denom, pgcd, NULL);
		Tree* tr = (!strcmp(b.nombre, "1")) ? new_tree(a.nombre) : join(new_tree(a.nombre), new_tree(b.nombre), fnc[DIVID].ex);
		free(pgcd.nombre); free(a.nombre); free(b.nombre);
		return tr;
	}
	Number w = divid(num, denom);
	Tree* tr = new_tree(w.nombre);
	free(w.nombre);
	return tr;
}

static Tree* perform_operation(char* left, char* right, NumberOperation* oper)
{
	Number a = { 1, left }, b = { 1, right };
	Number ret = oper(a, b);
	Tree* tr = new_tree(ret.nombre);
	free(ret.nombre);
	if (ret.signe != 1)
		return join(tr, NULL, fnc[NEGATIF].ex);
	return tr;
}

static Tree* factOp(const char* left)
{
	return new_tree(tostr(factoriel(strtoull(left, NULL, 10))));
}

static Tree* simplify_rational_number(Tree* u)
{
	if (count_tree_nodes(u) == 3 && u->tok_type == DIVID)
		return fracOp(u->tleft, u->tright);
	if (u->tok_type == NEGATIF)
		return join(simplify_rational_number(u->tleft), NULL, fnc[NEGATIF].ex);
	return clone(u);
}

static Tree* evaluate_quotient(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0"))
		return clone(left);
	Tree* t = numerator_fun(right);
	if (!strcmp(t->value, "0"))
	{
		clean_tree(t);
		return new_tree(fnc[UNDEF].ex);
	}
	Tree* i = simplify_RNE_rec(join(numerator_fun(left), denominator_fun(right), fnc[PROD].ex));
	Tree* j = simplify_RNE_rec(join(t, denominator_fun(left), fnc[PROD].ex));
	int k = count_tree_nodes(i), l = count_tree_nodes(j);
	Tree* tr = NULL;
	if (k == 1 && l == 1)
		tr = fracOp(i, j);
	else if (k == 2 && l == 1 && i->tok_type == NEGATIF)
		tr = join(fracOp(i->tleft, j), NULL, fnc[NEGATIF].ex);
	else if (l == 2 && k == 1 && j->tok_type == NEGATIF)
		tr = join(fracOp(i, j->tleft), NULL, fnc[NEGATIF].ex);
	else if (k == 2 && k == l && j->tok_type == NEGATIF && j->tok_type == i->tok_type)
		tr = fracOp(i->tleft, j->tleft);
	else
		tr = join(clone(i), clone(j), fnc[DIVID].ex);
	clean_tree(i);
	clean_tree(j);
	return tr;
}

static Tree* evaluate_power(Tree* bas, Tree* exposant)
{
	Tree* tr = numerator_fun(bas);
	bool is_zero = !strcmp(tr->value, "0");
	clean_tree(tr);
	if (is_zero)
	{
		if (!strcmp(exposant->value, "0") || exposant->tok_type == NEGATIF)
			return new_tree(fnc[UNDEF].ex);
		return new_tree("0");
	}
	if (!strcmp(exposant->value, "0"))
		return new_tree("1");
	if (!strcmp(exposant->value, "1"))
		return clone(bas);
	if (exposant->tok_type == NEGATIF)
	{
		Tree* r = new_tree("1"), * s = evaluate_power(bas, exposant->tleft);
		Tree* t = evaluate_quotient(r, s);
		clean_tree(r); clean_tree(s);
		return t;
	}
	if (bas->tok_type == DIVID)
	{
		Tree* n = numerator_fun(bas), * d = denominator_fun(bas);
		Tree* num = evaluate_power(n, exposant), * denom = evaluate_power(d, exposant);
		clean_tree(n); clean_tree(d);
		Tree* t = evaluate_quotient(num, denom);
		clean_tree(num); clean_tree(denom);
		return t;
	}
	if (bas->gtype <= ENT && exposant->gtype <= ENT)
	{
		Number b = { 1, bas->value }, e = { 1, exposant->value };
		Number r = ExponentiationRapide(b, e);
		tr = new_tree(r.nombre);
		free(r.nombre);
		return tr;
	}
	if (bas->tok_type == NEGATIF && bas->tleft->gtype <= ENT && exposant->gtype == ENT)
	{
		Number b = { 1, bas->tleft->value }, e = { 1, exposant->value };
		Number r = ExponentiationRapide(b, e);
		tr = new_tree(r.nombre);
		free(r.nombre);
		int k = exposant->value[strlen(exposant->value) - 1] - '0';
		if ((double)k / 2 == k / 2)
			return tr;
		return join(tr, NULL, fnc[NEGATIF].ex);
	}
	return join(clone(bas), clone(exposant), fnc[POW].ex);
}

static Tree* evaluate_cc(Tree* left, Tree* right, token tok)
{
	Tree* u = numerator_fun(left), * v = denominator_fun(left);
	Tree* w = numerator_fun(right), * x = denominator_fun(right);
	Tree* xx = clone(x), * vv = clone(v);
	Tree* num1 = simplify_RNE_rec(join(u, x, fnc[PROD].ex)), * num2 = simplify_RNE_rec(join(v, w, fnc[PROD].ex));
	Tree* denom = simplify_RNE_rec(join(vv, xx, fnc[PROD].ex)), * num = simplify_RNE_rec(join(num1, num2, fnc[tok].ex));
	if (num->tok_type != NEGATIF)
		return simplify_RNE_rec(join(num, denom, fnc[DIVID].ex));
	Tree* tr = join(simplify_RNE_rec(join(num->tleft, denom, fnc[DIVID].ex)), NULL, fnc[NEGATIF].ex);
	clean_noeud(num);
	return tr;
}

static Tree* evaluate_add(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0"))
		return clone(right);
	if (!strcmp(right->value, "0"))
		return clone(left);
	if (count_tree_nodes(left) == 1 && count_tree_nodes(right) == 1)
		return perform_operation(left->value, right->value, add);
	else if (left->tok_type == NEGATIF)
		return evaluate_diff(right, left->tleft);
	else if (right->tok_type == NEGATIF)
		return evaluate_diff(left, right->tleft);
	return evaluate_cc(left, right, ADD);
}

static Tree* evaluate_diff(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0"))
		return (!strcmp(right->value, "0")) ? clone(left) : join(clone(right), NULL, fnc[NEGATIF].ex);
	if (!strcmp(right->value, "0"))
		return clone(left);
	if (count_tree_nodes(left) == 1 && count_tree_nodes(right) == 1)
		return perform_operation(left->value, right->value, sub);
	else if (left->tok_type == NEGATIF && right->tok_type == NEGATIF)
		return evaluate_diff(right->tleft, left->tleft);
	else if (left->tok_type == NEGATIF)
		return join(evaluate_add(left->tleft, right), NULL, fnc[NEGATIF].ex);
	else if (right->tok_type == NEGATIF)
		return evaluate_add(left, right->tleft);
	return evaluate_cc(left, right, SUB);
}

static Tree* evaluate_prod(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0") || !strcmp(right->value, "0"))
		return new_tree("0");
	if (count_tree_nodes(left) == 1 && count_tree_nodes(right) == 1)
		return perform_operation(left->value, right->value, prod);
	else if (left->tok_type == NEGATIF && right->tok_type == NEGATIF)
		return evaluate_prod(left->tleft, right->tleft);
	else if (left->tok_type == NEGATIF)
		return join(simplify_RNE_rec(join(clone(right), clone(left->tleft), fnc[PROD].ex)), NULL, fnc[NEGATIF].ex);
	else if (right->tok_type == NEGATIF)
		return join(simplify_RNE_rec(join(clone(left), clone(right->tleft), fnc[PROD].ex)), NULL, fnc[NEGATIF].ex);
	Tree* u = numerator_fun(left), * v = denominator_fun(left);
	Tree* w = numerator_fun(right), * x = denominator_fun(right);
	Tree* num = simplify_RNE_rec(join(u, w, fnc[PROD].ex)), * denom = simplify_RNE_rec(join(v, x, fnc[PROD].ex));
	return simplify_RNE_rec(join(num, denom, fnc[DIVID].ex));
}

static Tree* simplify_RNE_rec(Tree* u)
{
	if (u->gtype < VAR)
	{
		Tree* t = clone(u);
		clean_tree(u);
		return t;
	}
	else if (count_tree_nodes(u) == 3 && u->tok_type == DIVID)
	{
		if (!strcmp(u->tright->value, "0"))
		{
			clean_tree(u);
			return new_tree(fnc[UNDEF].ex);
		}
		Tree* t = simplify_rational_number(u);
		clean_tree(u);
		return t;
	}
	else if (u->tok_type == NEGATIF)
	{
		if (!strcmp(u->tleft->value, "0"))
		{
			clean_tree(u);
			return new_tree("0");
		}
		if (count_tree_nodes(u) == 2)
		{
			Tree* r = clone(u);
			clean_tree(u);
			return r;
		}
		if (u->tleft->tok_type == NEGATIF)
		{
			Tree* r = clone(u->tleft->tleft);
			clean_tree(u);
			return simplify_RNE_rec(r);
		}
		Tree* t = join(new_tree("1"), NULL, fnc[NEGATIF].ex);
		Tree* tr = simplify_RNE_rec(join(t, simplify_RNE_rec(u->tleft), fnc[PROD].ex));
		clean_noeud(u);
		return tr;
	}
	else if (u->tok_type == FACTORIEL_F)
	{
		Tree* t = simplify_RNE_rec(u->tleft);
		clean_noeud(u);
		if (t->gtype == ENT)
		{
			Tree* ret = factOp(t->value);
			clean_tree(t);
			return ret;
		}
		return join(t, NULL, fnc[FACTORIEL_F].ex);
	}
	else if (u->tok_type == ABS_F)
	{
		Tree* tr = clone(u->tleft);
		clean_tree(u);
		return (Eval(tr) < 0) ? simplify_RNE_rec(join(tr, NULL, fnc[NEGATIF].ex)) : tr;
	}
	else
	{
		Tree* v = simplify_RNE(u->tleft), * w = simplify_RNE(u->tright);
		clean_noeud(u);
		if (v->tok_type == UNDEF || w->tok_type == UNDEF)
		{
			clean_tree(v);
			clean_tree(w);
			return new_tree(fnc[UNDEF].ex);
		}
		else
		{
			Tree* tr = NULL;
			if (u->tok_type == ADD)
				tr = evaluate_add(v, w);
			else if (u->tok_type == POW)
				tr = evaluate_power(v, w);
			else if (u->tok_type == SUB)
				tr = evaluate_diff(v, w);
			else if (u->tok_type == PROD)
				tr = evaluate_prod(v, w);
			else if (u->tok_type == DIVID)
				tr = evaluate_quotient(v, w);
			clean_tree(v);
			clean_tree(w);
			return tr;
		}
	}
}

static Tree* simplify_RNE(Tree* u)
{
	Tree* v = simplify_RNE_rec(u);
	if (v->tok_type == UNDEF)
		return v;
	Tree* tr = simplify_rational_number(v);
	clean_tree(v);
	return tr;
}

Tree* factorn(int val)
{
	Tree* tr = NULL;
	int f = 2, e = 0;
	double m = sqrt(val);
	while (f <= m)
	{
		while (fpart((double)val / f) == 0)
		{
			e++;
			val /= f;
		}
		if (e > 0)
		{
			Tree* t = (e == 1) ? new_tree(tostr(f)) : join(new_tree(tostr(f)), new_tree(tostr(e)), fnc[POW].ex);
			tr = (tr != NULL) ? join(tr, t, fnc[PROD].ex) : t;
			e = 0;
			m = sqrt(val);
		}
		f = (f == 2) ? 3 : f + 2;
	}
	if (val != 1)
		tr = (tr != NULL) ? join(tr, new_tree(tostr(val)), fnc[PROD].ex) : new_tree(tostr(val));
	return tr;
}

static Tree* trigo_simplify(Tree* u, token tk)
{
	if ((((COS_F <= tk && tk <= TAN_F) || (COSH_F <= tk && tk <= TANH_F)) && tk + 3 == u->tok_type) || (((ACOS_F <= tk && tk <= ATAN_F) || (ACOSH_F <= tk && tk <= ATANH_F)) && tk - 3 == u->tok_type))
	{
		Tree* t = simplify(clone(u->tleft));
		clean_tree(u);
		return t;
	}
	if (tk == COS_F && is_negation(u))
	{
		u = simplify(join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), u, fnc[PROD].ex));
		return trigo_simplify(u, tk);
	}
	if (tk == ACOS_F && is_negation(u))
	{
		u = simplify(join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), u, fnc[PROD].ex));
		return simplify(join(trigo_simplify(u, ASIN_F), join(new_tree("2"), new_tree(fnc[PI].ex), fnc[DIVID].ex), fnc[ADD].ex));
	}
	if ((tk == SIN_F || tk == TAN_F || tk == ASIN_F || tk == ATAN_F) && is_negation(u))
	{
		u = simplify(join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), u, fnc[PROD].ex));
		return simplify(join(trigo_simplify(u, tk), NULL, fnc[NEGATIF].ex));
	}
	if ((isconstant(u) || found_element(u, fnc[PI].ex)) && (tk == COS_F || tk == SIN_F || tk == TAN_F))
	{
		u = pow_transform(u);
		string su = Post2in(u, fnc);
		Tree* s = trigo_identify(su, tk);
		free(su);
		if (s != NULL)
		{
			clean_tree(u);
			return s;
		}
		Tree* c = coefficient_gpe(u, fnc[PI].ex, 1);
		if (fabs(Eval(c)) > 3.14)
		{
			clean_tree(u);
			Tree* cst = simplify(join(PGCD(c, new_tree("2")), new_tree("1"), fnc[SUB].ex));
			cst = join(cst, new_tree(fnc[PI].ex), fnc[PROD].ex);
			return trigo_simplify(cst, tk);
		}
		clean_tree(c);
	}
	return join(u, NULL, fnc[tk].ex);
}

static Tree* log_substitute(Tree* u, token tk, Tree* b)
{
	if (u->tok_type == LN_F)
	{
		free(u->value);
		u->value = strdup(fnc[tk].ex);
		u->tok_type = tk;
		if (!b && !strcmp(u->tleft->value, "10"))
		{
			clean_tree(u);
			return new_tree("1");
		}
		if (b != NULL)
		{
			if (tree_compare(b, u->tleft))
			{
				clean_tree(u);
				return new_tree("1");
			}
			u->tleft = join(u->tleft, clone(b), fnc[SEPARATEUR].ex);
		}
	}
	if (u->gtype == OPERAT)
	{
		u->tleft = log_substitute(u->tleft, tk, b);
		u->tright = log_substitute(u->tright, tk, b);
	}
	if (u->tok_type == NEGATIF)
		u->tleft = log_substitute(u->tleft, tk, b);
	return u;
}

static Tree* simp_rules(Tree* u, map* v)
{
	map d = map_create(u);
	mapCell* k = d->begin->next;
	clean_tree(u);
	u = clone(d->begin->data);
	while (k != NULL)
	{
		*v = push_back_map(*v, k->data);
		k = k->next;
	}
	d = clear_map(d);
	return u;
}

/* symbolic simplify */

static Tree* simplify_integer_power(Tree* v, Tree* w)
{
	if (v->gtype < VAR || (3 == count_tree_nodes(v) && v->tok_type == DIVID && v->tleft->gtype < VAR && v->tright->gtype < VAR))
		return simplify_RNE(join(v, w, fnc[POW].ex));
	else if (!strcmp("2", w->value) && v->tok_type == SIN_F && TRIG_EXPAND)
	{
		Tree* s = join(new_tree("1"), join(join(v->tleft, NULL, fnc[COS_F].ex), w, fnc[POW].ex), fnc[SUB].ex);
		clean_noeud(v);
		return s;
	}
	if (v->tok_type == IMAGE)
	{
		double a = tonumber(w->value);
		clean_tree(v); clean_tree(w);
		if (a / 4 == (int)(a / 4))
			return new_tree("1");
		else if (a / 4 > (int)(a / 4))
			return new_tree(fnc[IMAGE].ex);
		else if (a / 2 == (int)(a / 2))
			return join(new_tree("1"), NULL, fnc[NEGATIF].ex);
		return join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), new_tree(fnc[IMAGE].ex), fnc[PROD].ex);
	}
	if ((v->tok_type == ADD || v->tok_type == SUB) && (int)Eval(w) <= 10 && ALG_EXPAND)
	{
		Tree* tr = join(v, w, fnc[POW].ex);
		Tree* s = expand_main_op(tr);
		clean_tree(tr);
		return simplify(s);
	}
	if (!strcmp("2", w->value) && v->tok_type == COS_F)
		TRIG_EXPAND = true;
	return join(v, w, fnc[POW].ex);
}

static Tree* simplify_power(Tree* v, Tree* w)
{
	if (!strcmp(v->value, fnc[UNDEF].ex) || !strcmp(w->value, fnc[UNDEF].ex))
	{
		clean_tree(v);
		clean_tree(w);
		return new_tree(fnc[UNDEF].ex);
	}
	else if (!strcmp(v->value, "0"))
	{
		if (is_symbolic(w))
		{
			double t = Eval(w);
			clean_tree(v);
			clean_tree(w);
			return (t > 0) ? new_tree("0") : new_tree(fnc[UNDEF].ex);
		}
		return join(v, w, fnc[POW].ex);
	}
	else if (!strcmp(v->value, "1") || !strcmp("1", w->value))
	{
		clean_tree(w);
		return v;
	}
	else if (!strcmp("0", w->value))
	{
		clean_tree(v);
		clean_tree(w);
		return new_tree("1");
	}
	else if (v->tok_type == EXP_F)
	{
		v->tleft = join(w, v->tleft, fnc[PROD].ex);
		return simplify(v);
	}
	else if (v->tok_type == PROD || v->tok_type == DIVID)
	{
		v->tleft = simplify_power(v->tleft, clone(w));
		v->tright = simplify_power(v->tright, w);
		return v;
	}
	else if (v->tok_type == POW)
	{
		v->tright = simplify(join(v->tright, w, fnc[PROD].ex));
		return v;
	}
	else if (w->gtype == ENT && ALG_EXPAND)
		return simplify_integer_power(v, w);
	else if (w->gtype == NEGATION)
	{
		Tree* tr = simplify(join(v, clone(w->tleft), fnc[POW].ex));
		clean_tree(w);
		if (tr->tok_type == POW && isdemi(tr->tright) && tr->tleft->gtype == ENT)
			return join(tr, clone(tr->tleft), fnc[DIVID].ex);
		if (tr->tok_type == DIVID)
		{
			w = tr->tleft;
			tr->tleft = tr->tright;
			tr->tright = w;
			return tr;
		}
		return join(new_tree("1"), tr, fnc[DIVID].ex);
	}
	else if (v->gtype == ENT)
	{
		Tree* f = factorn(strtoull(v->value, NULL, 10));
		if (f->tok_type == POW)
		{
			clean_tree(v);
			f->tright = simplify(join(f->tright, w, fnc[PROD].ex));
			return f;
		}
		else if (f->tok_type == PROD)
		{
			clean_tree(v);
			map L = map_create_prod(f);
			clean_tree(f);
			Tree* s = new_tree("1"), * q = new_tree("1");
			mapCell* item = L->begin;
			while (item != NULL)
			{
				if (((Tree*)item->data)->tok_type == POW)
				{
					Tree* k = simplify_power(clone(item->data), clone(w));
					if (k->gtype == ENT)
						s = simplify(join(s, k, fnc[PROD].ex));
					else if (k->tok_type == PROD)
					{
						s = simplify(join(s, k->tleft, fnc[PROD].ex));
						q = join(q, k->tright, fnc[PROD].ex);
						clean_noeud(k);
					}
					else
						q = join(q, k, fnc[PROD].ex);
				}
				else
					q = join(q, join(clone(item->data), clone(w), fnc[POW].ex), fnc[PROD].ex);
				item = item->next;
			}
			L = clear_map(L);
			clean_tree(w);
			if (strcmp(q->value, "1"))
			{
				RT_SIMP = true;
				return join(s, Contract_pow(q), fnc[PROD].ex);
			}
			clean_tree(q);
			return s;
		}
		clean_tree(f);
		if (w->tok_type == DIVID && w->tleft->gtype == ENT && w->tright->gtype == ENT)
		{
			int n = (int)tonumber(w->tleft->value), d = (int)tonumber(w->tright->value);
			int q = (int)(n / d), r = (int)(n % d);
			if (q > 0)
			{
				Tree* bs = simplify(join(clone(v), new_tree(tostr(q)), fnc[POW].ex));
				Tree* xp = join(new_tree(tostr(r)), clone(w->tright), fnc[DIVID].ex);
				clean_tree(w);
				return join(bs, join(v, xp, fnc[POW].ex), fnc[PROD].ex);
			}
		}
	}
	else if (v->tok_type == NEGATIF && isconstant(v) && w->tok_type == DIVID && !strcmp(w->tright->value, "2"))
	{
		Tree* p = clone(v->tleft), * r = clone(w->tleft);
		clean_tree(v);
		return simplify(join(simplify_power(p, w), simplify_integer_power(new_tree(fnc[IMAGE].ex), r), fnc[PROD].ex));
	}
	return join(v, w, fnc[POW].ex);
}

static map merge(map p, map q, token tk)
{
	if (!q)
		return p;
	if (!p)
		return q;
	Tree* p1 = p->begin->data, * q1 = q->begin->data;
	map t = push_back_map(push_back_map(NULL, p1), q1);
	map h = simplify_oper_rec(t, tk);
	if (!h)
	{
		p = pop_front_map(p);
		q = pop_front_map(q);
		return merge(p, q, tk);
	}
	if (h->length == 1)
	{
		p = pop_front_map(p);
		q = pop_front_map(q);
		map L = push_front_map(merge(p, q, tk), h->begin->data);
		h = clear_map(h);
		return simplify_oper_rec(L, tk);
	}
	if (tree_compare(h->begin->data, p1))
		p = pop_front_map(p);
	else
		q = pop_front_map(q);
	map L = push_front_map(merge(p, q, tk), h->begin->data);
	h = clear_map(h);
	return L;
}

static map simplify_sum_fct(Tree* u1, Tree* u2)
{
	Tree* v = denominator_fun(u1), * x = denominator_fun(u2);
	bool i = strcmp(v->value, "1"), k = strcmp(x->value, "1");
	clean_tree(v); clean_tree(x);
	if (ALG_EXPAND && (i || k))
		return push_back(NULL, rationalize_sum(u1, u2, fnc[ADD].ex));
	token tok_u1 = u1->tok_type, tok_u2 = u2->tok_type;
	if (tok_u1 == tok_u2 && (LN_F == tok_u1 || LOG_F == tok_u1))
	{
		Tree* w = join(simplify(join(clone(u1->tleft), clone(u2->tleft), fnc[PROD].ex)), NULL, u2->value);
		return push_back(NULL, w);
	}
	if (tok_u1 == tok_u2 && tok_u1 == LOGBASE_F && tree_compare(u1->tleft->tright, u2->tleft->tright))
	{
		Tree* w = join(join(simplify(join(clone(u1->tleft->tleft), clone(u2->tleft->tleft), fnc[PROD].ex)), clone(u1->tleft->tright), fnc[SEPARATEUR].ex), NULL, u2->value);
		return push_back(NULL, w);
	}
	map map_u1 = map_create_prod(u1), map_u2 = map_create_prod(u2);
	Tree* fact_com = new_tree("1");
	mapCell* tmp0 = map_u1->begin, * tmp1 = NULL;
	while (tmp0 != NULL)
	{
		tmp1 = map_u2->begin;
		while (tmp1 != NULL)
		{
			if (tree_compare(tmp1->data, tmp0->data) && !isconstant(tmp1->data))
			{
				fact_com = join(fact_com, clone(tmp0->data), fnc[PROD].ex);
				clean_tree(tmp1->data);
				tmp1->data = new_tree("1");
				clean_tree(tmp0->data);
				tmp0->data = new_tree("1");
				break;
			}
			tmp1 = tmp1->next;
		}
		tmp0 = tmp0->next;
	}
	if (strcmp(fact_com->value, "1"))
	{
		Tree* term_u1 = construct(fnc[PROD].ex, &map_u1), * term_u2 = construct(fnc[PROD].ex, &map_u2);
		v = simplify(join(term_u1, term_u2, fnc[ADD].ex));
		bool k = !strcmp(v->value, "1");
		if (!strcmp(v->value, "0") || k)
		{
			map q = (k) ? push_back_map(NULL, fact_com) : NULL;
			clean_tree(v);
			clean_tree(fact_com);
			return q;
		}
		return push_back(NULL, join(v, fact_com, fnc[PROD].ex));
	}
	clean_tree(fact_com);
	map_u1 = clear_map(map_u1);
	map_u2 = clear_map(map_u2);
	return push_back_map(push_back_map(NULL, u1), u2);
}

static map simplify_oper_rec(map L, token tk)
{
	if (L->length == 1)
		return L;
	Tree* u1 = L->begin->data, * u2 = L->end->data;
	token tok = (tk == PROD) ? DIVID : SUB, u1tok = u1->tok_type, u2tok = u2->tok_type;
	const char* nb = (tk == PROD) ? "1" : "0";
	if (L->length == 2 && (u1tok != tk && u1tok != tok) && (u2tok != tk && u2tok != tok))
	{
		if (isconstant(u1) && isconstant(u2))
		{
			Tree* p = simplify_RNE(join(clone(u1), clone(u2), fnc[tk].ex));
			L = clear_map(L);
			if (!strcmp(p->value, nb))
			{
				clean_tree(p);
				return L;
			}
			L = push_back(L, p);
			return L;
		}
		if (!strcmp(u1->value, nb))
		{
			L = pop_front_map(L);
			return L;
		}
		if (!strcmp(u2->value, nb))
		{
			L = pop_back_map(L);
			return L;
		}
		if (tk == PROD)
		{
			if (tree_compare(base(u1), base(u2)) && !isconstant(u1) && !isconstant(u2))
			{
				Tree* s = simplify(join(clone(base(u1)), join(exponent(u1), exponent(u2), fnc[ADD].ex), fnc[POW].ex));
				L = clear_map(L);
				map q = (!strcmp(s->value, nb)) ? NULL : push_back_map(L, s);
				clean_tree(s);
				return q;
			}
			if (u1->tok_type == EXP_F && u2->tok_type == EXP_F)
			{
				Tree* s = simplify(join(join(clone(u1->tleft), clone(u2->tleft), fnc[ADD].ex), NULL, fnc[EXP_F].ex));
				L = push_back(clear_map(L), s);
				return L;
			}
			if (u1->tok_type == POW && u2->tok_type == POW && tree_compare(u1->tright, u2->tright) && isconstant(u1->tleft) && isconstant(u2->tleft))
			{
				Tree* s = simplify(join(join(clone(u1->tleft), clone(u2->tleft), fnc[PROD].ex), clone(u1->tright), fnc[POW].ex));
				L = push_back(clear_map(L), s);
				return L;
			}
		}
		if (tk == ADD)
		{
			if (tree_compare(u1, u2))
			{
				Tree* s = simplify(join(new_tree("2"), clone(u1), fnc[PROD].ex));
				return push_back(clear_map(L), s);
			}
			map li = simplify_sum_fct(u1, u2);
			if (li == NULL || li->length == 1)
			{
				L = clear_map(L);
				return li;
			}
			li = clear_map(li);
		}
		if (ordre_tree(u2, u1))
		{
			L->begin->data = u2;
			L->end->data = u1;
			return L;
		}
		return L;
	}
	else if (L->length == 2 && (u1tok == tk || u1tok == tok || u2tok == tk || u2tok == tok))
	{
		map p = (tk == PROD) ? map_create_prod(u1) : map_create_add(u1), q = (tk == PROD) ? map_create_prod(u2) : map_create_add(u2);
		L = clear_map(L);
		return merge(p, q, tk);
	}
	else if (isconstant(u1) && isconstant(L->begin->next->data))
	{
		Tree* p = simplify_RNE(join(clone(u1), clone(L->begin->next->data), fnc[tk].ex));
		L = push_front(pop_front_map(pop_front_map(L)), p);
		return simplify_oper_rec(L, tk);
	}
	map k = (tk == PROD) ? map_create_prod(u1) : map_create_add(u1);
	L = pop_front_map(L);
	return merge(k, simplify_oper_rec(L, tk), tk);
}

static Tree* simplify_oper(map L, token tk)
{
	mapCell* tmp = L->begin;
	while (tmp != NULL)
	{
		if (!strcmp(((Tree*)tmp->data)->value, fnc[UNDEF].ex) || (tk == PROD && !strcmp(((Tree*)tmp->data)->value, "0")))
		{
			Tree* t = clone(tmp->data);
			L = clear_map(L);
			return t;
		}
		tmp = tmp->next;
	}
	map v = simplify_oper_rec(L, tk);
	if (v == NULL)
		return new_tree((tk == PROD) ? "1" : "0");
	v = map_sort(v);
	return construct(fnc[tk].ex, &v);
}

static Tree* construct(const char* op, map* L)
{
	mapCell* tmp = (*L)->begin->next;
	Tree* tr = clone((*L)->begin->data);
	while (tmp != NULL)
	{
		tr = join(tr, clone(tmp->data), op);
		tmp = tmp->next;
	}
	*L = clear_map(*L);
	return tr;
}

Tree* simplify(Tree* u)
{
	token tk = u->tok_type;
	if (u->gtype <= VAR)
	{
		Tree* r = clone(u);
		clean_tree(u);
		return r;
	}
	if (isconstant(u))
		return simplify_RNE(u);
	if (tk == SIGN_F)
	{
		u->tleft = simplify(u->tleft);
		if (isconstant(u->tleft))
		{
			double q = Eval(u->tleft);
			clean_tree(u);
			if (q == 0)
				return new_tree("0");
			Tree* t = new_tree("1");
			if (q < 0)
				t = join(t, NULL, fnc[NEGATIF].ex);
			return t;
		}
		Tree* r = clone(u);
		clean_tree(u);
		return r;
	}
	if (tk == SQRT_F || tk == CBRT_F)
	{
		if (u->tleft->tok_type == NEGATIF && tk == SQRT_F && isconstant(u->tleft))
		{
			Tree* tr = simplify(join(clone(u->tleft->tleft), join(new_tree("1"), new_tree("2"), fnc[DIVID].ex), fnc[POW].ex));
			clean_tree(u);
			return join(tr, new_tree(fnc[IMAGE].ex), fnc[PROD].ex);
		}
		if (!strcmp(u->tleft->value, "0"))
		{
			Tree* tr = u->tleft;
			clean_noeud(u);
			return tr;
		}
		Tree* tr = simplify(join(clone(u->tleft), join(new_tree("1"), new_tree((tk == SQRT_F) ? "2" : "3"), fnc[DIVID].ex), fnc[POW].ex));
		clean_tree(u);
		return tr;
	}
	if (tk == NEGATIF)
	{
		Tree* tr = simplify(join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), u->tleft, fnc[PROD].ex));
		clean_noeud(u);
		return tr;
	}
	if (tk == EXP_F || tk == LN_F)
	{
		u->tleft = simplify(u->tleft);
		Tree* t = (tk == EXP_F) ? simplify_exp(u) : simplify_ln(u);
		clean_tree(u);
		return t;
	}
	if (tk == LOGBASE_F || tk == LOG_F)
	{
		bool k = u->tleft->tok_type == SEPARATEUR;
		Tree* q = join(simplify(clone(k ? u->tleft->tleft : u->tleft)), NULL, fnc[LN_F].ex), * w = k ? clone(u->tleft->tright) : NULL;
		clean_tree(u);
		Tree* v = simplify_ln(q);
		clean_tree(q);
		if (v->tok_type == UNDEF)
		{
			clean_tree(w);
			return v;
		}
		if (tk == LOGBASE_F && !strcmp(w->value, "10"))
		{
			tk = LOG_F;
			clean_tree(w);
			w = NULL;
		}
		q = log_substitute(v, tk, w);
		clean_tree(w);
		return q;
	}
	if (tk == ABS_F)
	{
		u->tleft = simplify(u->tleft);
		Tree* t = absolute_value(u->tleft);
		clean_tree(u);
		return t;
	}
	if (tk == COS_F || tk == SIN_F || tk == ACOS_F || tk == ASIN_F)
	{
		Tree* r = trigo_simplify(simplify(u->tleft), tk);
		clean_noeud(u);
		return r;
	}
	if (tk == TAN_F || tk == ATAN_F || tk == TANH_F || tk == ATANH_F)
	{
		u->tleft = simplify(u->tleft);
		Tree* r = trigo_simplify(u->tleft, tk);
		clean_noeud(u);
		if (r->tok_type != tk)
			return r;
		Tree* v = join(clone(r->tleft), NULL, fnc[tk - 1].ex), * w = join(clone(r->tleft), NULL, fnc[tk - 2].ex);
		clean_tree(r);
		return join(v, w, fnc[DIVID].ex);
	}
	if (tk == ROOT_F)
	{
		Tree* tr = simplify(join(clone(u->tleft->tleft), join(new_tree("1"), clone(u->tleft->tright), fnc[DIVID].ex), fnc[POW].ex));
		clean_tree(u);
		return tr;
	}
	if (EXP_F <= tk && tk < ROOT_F)
	{
		Tree* t = join(simplify(u->tleft), NULL, u->value);
		clean_noeud(u);
		return t;
	}
	if (tk == POW)
	{
		Tree* v = simplify(u->tleft), * w = simplify(u->tright);
		clean_noeud(u);
		return simplify_power(v, w);
	}
	if (tk == DIVID)
	{
		string vr = variable(u);
		if (vr != NULL && ispoly(u->tleft, vr) && ispoly(u->tright, vr) && !ismonomial(u->tleft, vr) && !ismonomial(u->tright, vr))
		{
			Tree* dn = degree_sv(u->tleft, vr), * dd = degree_sv(u->tright, vr);
			bool a = strcmp(dn->value, "0"), b = strcmp(dd->value, "0");
			clean_tree(dd); clean_tree(dn);
			if (a && b)
			{
				Tree* tr = poly_simp(polycoeffs(u->tleft, vr), polycoeffs(u->tright, vr), vr);
				free(vr);
				clean_tree(u);
				return tr;
			}
		}
		free(vr);
	}
	if (ADD <= tk && tk <= DIVID)
	{
		if (tk == PROD || tk == DIVID)
		{
			LN_EXP_EXPAND = false;
			Tree* r = expand_main_op(u);
			clean_tree(u);
			u = r;
			tk = u->tok_type;
		}
		bool cplx = (tk == DIVID && found_element(u->tright, fnc[IMAGE].ex));
		if (tk == ADD || tk == SUB)
		{
			Tree* f = rationalize_expression(u);
			clean_tree(u);
			u = f;
			tk = u->tok_type;
		}
		map v = map_create(u);
		clean_tree(u);
		mapCell* tmp = v->begin;
		while (tmp != NULL)
		{
			if (((Tree*)tmp->data)->gtype > VAR)
			{
				tmp->data = simplify(tmp->data);
				if ((tk == PROD || tk == DIVID) && ((Tree*)tmp->data)->tok_type == PROD)
					tmp->data = simp_rules(tmp->data, &v);
				else if ((tk == ADD || tk == SUB) && ((Tree*)tmp->data)->tok_type == PROD)
				{
					Tree* r = expand_main_op(tmp->data);
					clean_tree(tmp->data);
					tmp->data = r;
					if (r->tok_type == ADD || r->tok_type == SUB)
						tmp->data = simp_rules(tmp->data, &v);
				}
			}
			tmp = tmp->next;
		}
		Tree* ret = NULL;
		v = map_sort(v);
		ret = simplify_oper(v, (tk == PROD || tk == DIVID) ? PROD : ADD);
		if (cplx)
		{
			Tree* tr = pow_transform(ret);
			if (tr->tok_type == DIVID && found_element(tr->tright, fnc[IMAGE].ex))
			{
				map cf = polycoeffs(tr->tright, fnc[IMAGE].ex);
				Tree* z = simplify(join(clone(tr->tleft), join(clone(cf->begin->data), join(clone(cf->end->data), new_tree(fnc[IMAGE].ex), fnc[PROD].ex), fnc[SUB].ex), fnc[PROD].ex));
				Tree* o = simplify(join(join(clone(cf->begin->data), new_tree("2"), fnc[POW].ex), join(clone(cf->end->data), new_tree("2"), fnc[POW].ex), fnc[ADD].ex));
				clean_tree(tr); cf = clear_map(cf);
				return simplify(join(z, o, fnc[DIVID].ex));
			}
			return tr;
		}
		return ret;
	}
	Tree* r = clone(u);
	clean_tree(u);
	return r;
}

static Tree* denom_com(Tree* m, Tree* n, Tree* r, Tree* s, const char* op)
{
	List vrs = NULL;
	vrs = getvars(s, getvars(r, vrs));
	if (vrs == NULL)
		return NULL;
	if (vrs->length == 1 && ispoly(r, vrs->begin->data) && ispoly(s, vrs->begin->data))
	{
		map coef_r = polycoeffs(r, vrs->begin->data), coef_s = polycoeffs(s, vrs->begin->data);
		clean_tree(r); clean_tree(s);
		map GCD = poly_gcd(coef_r, coef_s);
		map quot_r = poly_quotient(coef_r, GCD, INT_F), quot_s = poly_quotient(coef_s, GCD, INT_F);
		coef_r = clear_map(coef_r); coef_s = clear_map(coef_s);
		Tree* qr = polyreconstitute(&quot_r, vrs->begin->data), * qs = polyreconstitute(&quot_s, vrs->begin->data);
		Tree* g = polyreconstitute(&GCD, vrs->begin->data);
		vrs = clear_dlist(vrs);
		Tree* dr = simplify(join(g, join(clone(qs), clone(qr), fnc[PROD].ex), fnc[PROD].ex));
		m = simplify(join(m, qs, fnc[PROD].ex));
		n = simplify(join(n, qr, fnc[PROD].ex));
		return join(join(m, n, op), dr, fnc[DIVID].ex);
	}
	vrs = clear_dlist(vrs);
	return NULL;
}

static Tree* rationalize_sum(Tree* u, Tree* v, const char* op)
{
	Tree* r = denominator_fun(u), * s = denominator_fun(v);
	if (!strcmp(r->value, "1") && !strcmp(s->value, "1"))
	{
		clean_tree(r); clean_tree(s);
		return join(clone(u), clone(v), op);
	}
	Tree* m = numerator_fun(u), * n = numerator_fun(v);
	if (tree_compare(r, s))
	{
		clean_tree(r);
		Tree* tr = rationalize_sum(m, n, op);
		clean_tree(m); clean_tree(n);
		return join(tr, s, fnc[DIVID].ex);
	}
	if (r->gtype == ENT && s->gtype == ENT)
	{
		Number a = { 1, r->value }, b = { 1, s->value };
		Number p = gcd(a, b);
		if (strcmp(p.nombre, "1"))
		{
			Tree* pt = new_tree(p.nombre);
			free(p.nombre);
			r = simplify(join(r, clone(pt), fnc[DIVID].ex));
			s = simplify(join(s, clone(pt), fnc[DIVID].ex));
			n = simplify(join(clone(r), n, fnc[PROD].ex));
			m = simplify(join(clone(s), m, fnc[PROD].ex));
			s = simplify(join(pt, join(r, s, fnc[PROD].ex), fnc[PROD].ex));
			return join(join(m, n, op), s, fnc[DIVID].ex);
		}
		free(p.nombre);
	}
	Tree* ret = denom_com(m, n, r, s, op);
	if (ret != NULL)
		return ret;
	Tree* d = simplify(join(clone(r), clone(s), fnc[PROD].ex));
	Tree* a = simplify(join(m, s, fnc[PROD].ex)), * b = simplify(join(n, r, fnc[PROD].ex));
	Tree* tr = rationalize_sum(a, b, op);
	clean_tree(a); clean_tree(b);
	return join(tr, d, fnc[DIVID].ex);
}

Tree* rationalize_expression(Tree* u)
{
	token tk = u->tok_type;
	if (tk == POW)
		return join(rationalize_expression(u->tleft), clone(u->tright), fnc[POW].ex);
	if (tk == PROD)
		return join(rationalize_expression(u->tleft), rationalize_expression(u->tright), fnc[PROD].ex);
	if (tk == ADD || tk == SUB)
	{
		Tree* v = rationalize_expression(u->tleft), * w = rationalize_expression(u->tright);
		Tree* tr = rationalize_sum(v, w, u->value);
		clean_tree(v); clean_tree(w);
		return tr;
	}
	return clone(u);
}

static Tree* contract_exp_rules(Tree* u)
{
	Tree* v = expand_main_op(u);
	if (v->tok_type == POW && v->tleft->tok_type == EXP_F)
	{
		Tree* p = join(clone(v->tright), clone(v->tleft->tleft), fnc[PROD].ex);
		clean_tree(v);
		Tree* s = contract_exp_rules(p);
		clean_tree(p);
		return join(s, NULL, fnc[EXP_F].ex);
	}
	else if (v->tok_type == PROD || v->tok_type == DIVID)
	{
		map L = map_create(v);
		clean_tree(v);
		Tree* s = new_tree("0"), * p = new_tree("1");
		mapCell* tmp = L->begin;
		while (tmp != NULL)
		{
			Tree* q = contract_exp_rules(tmp->data);
			clean_tree(tmp->data);
			tmp->data = q;
			if (q->tok_type == EXP_F)
				s = simplify(join(s, clone(q->tleft), fnc[ADD].ex));
			else
				p = simplify(join(p, clone(q), fnc[PROD].ex));
			tmp = tmp->next;
		}
		L = clear_map(L);
		if (!strcmp(s->value, "0"))
		{
			clean_tree(s);
			return p;
		}
		if (!strcmp(p->value, "1"))
		{
			clean_tree(p);
			return join(s, NULL, fnc[EXP_F].ex);
		}
		return join(p, join(s, NULL, fnc[EXP_F].ex), fnc[PROD].ex);
	}
	else if (v->tok_type == ADD)
	{
		map L = map_create(v);
		clean_tree(v);
		Tree* s = new_tree("0");
		mapCell* tmp = L->begin;
		while (tmp != NULL)
		{
			if (PROD <= ((Tree*)tmp->data)->tok_type && ((Tree*)tmp->data)->tok_type <= POW)
				s = join(s, contract_exp_rules(tmp->data), fnc[ADD].ex);
			else
				s = join(s, clone(tmp->data), fnc[PROD].ex);
			tmp = tmp->next;
		}
		L = clear_map(L);
		return s;
	}
	return v;
}

static Tree* contract_exp(Tree* u)
{
	if (u->gtype <= VAR || isconstant(u))
		return clone(u);
	token tk = u->tok_type;
	if (ADD <= tk && tk <= POW)
		return contract_exp_rules(u);
	return clone(u);
}

static Tree* expand_exp_rules(Tree* u)
{
	token tk = u->tok_type;
	if (tk == LN_F)
		return clone(u->tleft);
	if (!strcmp(u->value, "0"))
		return new_tree("1");
	if (tk == ADD || tk == SUB)
		return join(expand_exp_rules(u->tleft), expand_exp_rules(u->tright), fnc[PROD].ex);
	if (tk == PROD && isconstant(u->tleft))
		return join(expand_exp_rules(u->tright), clone(u->tleft), fnc[POW].ex);
	return join(clone(u), NULL, fnc[EXP_F].ex);
}

static Tree* expand_exp(Tree* u)
{
	return (u->tok_type == EXP_F) ? expand_exp_rules(u->tleft) : clone(u);
}

static Tree* simplify_exp(Tree* u)
{
	Tree* p = expand_exp(u);
	Tree* s = contract_exp(p);
	clean_tree(p);
	return s;
}

static Tree* contract_ln_rules(Tree* v)
{
	if (v->tok_type == ADD)
	{
		map L = map_create_add(v);
		Tree* p = NULL, * s = NULL;
		mapCell* item = L->begin;
		while (item != NULL)
		{
			Tree* q = contract_ln_rules(item->data);
			clean_tree(item->data);
			item->data = q;
			if (q->tok_type == LN_F)
				s = (s == NULL) ? clone(q->tleft) : join(s, clone(q->tleft), fnc[PROD].ex);
			else if (q->tok_type == NEGATIF && q->tleft->tok_type == LN_F)
			{
				Tree* w = join(new_tree("1"), clone(q->tleft->tleft), fnc[DIVID].ex);
				s = (s == NULL) ? w : join(s, w, fnc[PROD].ex);
			}
			else if (q->tok_type == PROD && q->tright->tok_type == LN_F)
			{
				Tree* w = join(clone(q->tright->tleft), clone(q->tleft), fnc[POW].ex);
				s = (s == NULL) ? w : join(s, w, fnc[PROD].ex);
			}
			else if (strcmp(q->value, "0"))
				p = (p == NULL) ? clone(q) : join(p, clone(q), fnc[ADD].ex);
			item = item->next;
		}
		L = clear_map(L);
		if (s == NULL)
			return simplify(p);
		if (p == NULL)
			return join(simplify(s), NULL, fnc[LN_F].ex);
		return join(simplify(p), join(simplify(s), NULL, fnc[LN_F].ex), fnc[ADD].ex);
	}
	if (v->tok_type == PROD || v->tok_type == DIVID)
	{
		map L = map_create_prod(v);
		Tree* s = NULL;
		mapCell* item = L->begin;
		while (item != NULL)
		{
			if (((Tree*)item->data)->tok_type == ADD || ((Tree*)item->data)->tok_type == SUB)
				s = (s == NULL) ? contract_ln_rules(item->data) : join(s, contract_ln_rules(item->data), fnc[ADD].ex);
			else
				s = (s == NULL) ? clone(item->data) : join(s, clone(item->data), fnc[PROD].ex);
			item = item->next;
		}
		L = clear_map(L);
		return s;
	}
	return clone(v);
}

static Tree* contract_ln(Tree* u)
{
	if (u->gtype <= VAR || isconstant(u))
		return clone(u);
	token tk = u->tok_type;
	if (tk >= ADD && tk < POW)
		return contract_ln_rules(u);
	return clone(u);
}

static Tree* expand_ln_rules(Tree* u)
{
	if (u->tok_type == EXP_F)
		return clone(u->tleft);
	if (!strcmp(u->value, "0"))
		return new_tree(fnc[UNDEF].ex);
	if (!strcmp(u->value, "1"))
		return new_tree("0");
	if (u->tok_type == PROD)
		return join(expand_ln_rules(u->tleft), expand_ln_rules(u->tright), fnc[ADD].ex);
	if (u->tok_type == DIVID)
		return join(expand_ln_rules(u->tleft), expand_ln_rules(u->tright), fnc[SUB].ex);
	if (u->tok_type == POW && is_symbolic(u->tleft))
		return join(clone(u->tright), expand_ln_rules(u->tleft), fnc[PROD].ex);
	if (u->gtype == ENT)
	{
		Tree* f = Contract_pow(factorn(strtoull(u->value, NULL, 10)));
		if (f->tok_type == POW)
		{
			Tree* ret = join(clone(f->tright), join(clone(f->tleft), NULL, fnc[LN_F].ex), fnc[PROD].ex);
			clean_tree(f);
			return ret;
		}
		clean_tree(f);
	}
	return join(clone(u), NULL, fnc[LN_F].ex);
}

static Tree* expand_ln(Tree* u)
{
	return (u->tok_type == LN_F) ? expand_ln_rules(u->tleft) : clone(u);
}

static Tree* simplify_ln(Tree* u)
{
	Tree* p = expand_ln(u);
	Tree* s = contract_ln(p);
	clean_tree(p);
	return s;
}

static Tree* absolute_value(Tree* u)
{
	if (u->gtype < VAR)
		return clone(u);
	if (u->tok_type == DIVID)
		return join(absolute_value(u->tleft), absolute_value(u->tright), u->value);
	if (u->tok_type == POW && u->tright->gtype == ENT)
		return join(absolute_value(u->tleft), clone(u->tright), fnc[POW].ex);
	if (u->tok_type == IMAGE)
		return new_tree("1");
	if (u->tok_type == NEGATIF)
		return absolute_value(u->tleft);
	if (u->tok_type == PROD)
	{
		map L = map_create_prod(u);
		Tree* s = new_tree("1"), * r = new_tree("1");
		mapCell* item = L->begin;
		while (item != NULL)
		{
			Tree* tmp = absolute_value(item->data);
			if (tmp->tok_type == ABS_F)
			{
				s = simplify(join(s, tmp->tleft, fnc[PROD].ex));
				clean_noeud(tmp);
			}
			else
				r = simplify(join(r, tmp, fnc[PROD].ex));
			item = item->next;
		}
		L = clear_map(L);
		return join(r, join(s, NULL, fnc[ABS_F].ex), fnc[PROD].ex);
	}
	if (u->tok_type == ADD && found_element(u, fnc[IMAGE].ex))
	{
		map cf = polycoeffs(u, fnc[IMAGE].ex);
		Tree* a = simplify(join(join(clone(cf->begin->data), new_tree("2"), fnc[POW].ex), join(clone(cf->end->data), new_tree("2"), fnc[POW].ex), fnc[ADD].ex));
		cf = clear_map(cf);
		return simplify(join(a, NULL, fnc[SQRT_F].ex));
	}
	return join(clone(u), NULL, fnc[ABS_F].ex);
}

Tree* Contract_pow(Tree* v)
{
	token tk = v->tok_type;
	if (tk == ADD || tk == DIVID || tk == POW)
	{
		v->tleft = Contract_pow(v->tleft);
		if (tk != POW)
			v->tright = Contract_pow(v->tright);
		return v;
	}
	else if (tk == PROD)
	{
		map L = map_create(v), q = NULL, s = NULL, p = NULL;
		clean_tree(v);
		mapCell* item = L->begin;
		while (item != NULL)
		{
			if (((Tree*)item->data)->tok_type == POW)
			{
				bool found = false;
				if (q != NULL)
				{
					mapCell* tmp = q->begin, * tmp1 = s->begin;
					while (tmp != NULL)
					{
						if (tree_compare(tmp->data, ((Tree*)item->data)->tright))
						{
							tmp1->data = join(tmp1->data, clone(((Tree*)item->data)->tleft), fnc[PROD].ex);
							if (RT_SIMP)
								tmp1->data = simplify(tmp1->data);
							found = true;
							break;
						}
						tmp = tmp->next;
						tmp1 = tmp1->next;
					}
				}
				if (!found)
				{
					q = push_back_map(q, ((Tree*)item->data)->tright);
					s = push_back_map(s, ((Tree*)item->data)->tleft);
				}
			}
			else
				p = push_back_map(p, item->data);
			item = item->next;
		}
		L = clear_map(L);
		if (q != NULL)
		{
			mapCell* tmp = q->begin, * tmp1 = s->begin;
			while (tmp != NULL)
			{
				p = push_back(p, join(clone(tmp1->data), clone(tmp->data), fnc[POW].ex));
				tmp = tmp->next;
				tmp1 = tmp1->next;
			}
			q = clear_map(q);
			s = clear_map(s);
			p = map_sort(p);
		}
		return construct(fnc[PROD].ex, &p);
	}
	return v;
}

Tree* algebraic_expand(Tree* u)
{
	Tree* tr = expand(u);
	clean_tree(u);
	TRIG_EXPAND = false;
	return simplify(tr);
}

/* polynomials */

bool ismonomial(Tree* u, const char* x)
{
	if (u->tok_type == POW)
		return ismonomial(u->tleft, x) && u->tright->gtype == ENT;
	if (u->tok_type == PROD)
		return ismonomial(u->tleft, x) && ismonomial(u->tright, x);
	if (u->tok_type == DIVID)
		return ismonomial(u->tleft, x) && !ismonomial(u->tright, x);
	if (u->tok_type == NEGATIF)
		return ismonomial(u->tleft, x);
	return (!strcmp(u->value, x) || !found_element(u, x));
}

static Tree* degree_monomial_sv(Tree* u, const char* x)
{
	if (!strcmp(u->value, "0"))
		return join(new_tree("1"), NULL, fnc[NEGATIF].ex);
	else if (isconstant(u))
		return new_tree("0");
	else if (!strcmp(u->value, x))
		return new_tree("1");
	else if (u->tok_type == POW && !strcmp(u->tleft->value, x) && u->tright->gtype == ENT && Eval(u->tright) >= 1)
		return clone(u->tright);
	else if (u->tok_type == NEGATIF || u->tok_type == DIVID)
		return degree_monomial_sv(u->tleft, x);
	else if (u->tok_type == PROD)
	{
		Tree* s = degree_monomial_sv(u->tleft, x), * t = degree_monomial_sv(u->tright, x);
		if (strcmp(s->value, fnc[UNDEF].ex) && strcmp(t->value, fnc[UNDEF].ex))
		{
			clean_tree(s);
			return t;
		}
		clean_tree(s);
		clean_tree(t);
	}
	return new_tree(fnc[UNDEF].ex);
}

Tree* degree_sv(Tree* u, const char* x)
{
	Tree* d = degree_monomial_sv(u, x);
	if (strcmp(d->value, fnc[UNDEF].ex))
		return d;
	clean_tree(d);
	if (u->tok_type == ADD || u->tok_type == SUB)
	{
		map L = map_create_add(u);
		mapCell* tmp = L->begin;
		d = new_tree("0");
		while (tmp != NULL)
		{
			Tree* f = degree_monomial_sv(tmp->data, x);
			if (!strcmp(f->value, fnc[UNDEF].ex))
			{
				clean_tree(d);
				L = clear_map(L);
				return f;
			}
			else if (Eval(d) < Eval(f))
			{
				clean_tree(d);
				d = clone(f);
			}
			clean_tree(f);
			tmp = tmp->next;
		}
		L = clear_map(L);
		return d;
	}
	else if (u->tok_type == DIVID)
		return degree_sv(u->tleft, x);
	else if (u->tok_type == PROD && isconstant(u->tleft))
		return degree_sv(u->tright, x);
	return new_tree(fnc[UNDEF].ex);
}

Tree* coefficient_gpe(Tree* u, const char* x, unsigned j)
{
	map cf = polycoeffs(u, x);
	mapCell* tmp = cf->begin;
	unsigned i = cf->length - 1;
	while (tmp != NULL)
	{
		if (i == j)
		{
			Tree* a = clone(tmp->data);
			cf = clear_map(cf);
			return a;
		}
		i--;
		tmp = tmp->next;
	}
	cf = clear_map(cf);
	return new_tree("0");
}

Tree* polyreconstitute(map* Li, const char* x)
{
	int n = (*Li)->length;
	mapCell* tmp = (*Li)->begin;
	Tree* u = NULL;
	while (tmp != NULL)
	{
		if (strcmp(((Tree*)tmp->data)->value, "0"))
		{
			Tree* v = clone(tmp->data);
			if (n > 2)
				v = join(v, join(new_tree(x), new_tree(tostr(n - 1)), fnc[POW].ex), fnc[PROD].ex);
			else if (n == 2)
				v = join(v, new_tree(x), fnc[PROD].ex);
			u = (u == NULL) ? v : join(v, u, fnc[ADD].ex);
		}
		n--;
		tmp = tmp->next;
	}
	(*Li) = clear_map(*Li);
	return u;
}


static bool iszero(map Li)
{
	Cell* celdivd = Li->begin;
	while (celdivd != NULL)
	{
		if (strcmp(((Tree*)celdivd->data)->value, "0"))
			return false;
		celdivd = celdivd->next;
	}
	return true;
}

static map remain(map divr, map divd, Tree* a)
{
	mapCell* t = divr->begin, * celdivd = divd->begin;
	while (t != NULL)
	{
		Tree* s = join(clone(a), clone(t->data), fnc[PROD].ex);
		celdivd->data = simplify(join(celdivd->data, s, fnc[SUB].ex));
		t = t->next;
		celdivd = celdivd->next;
	}
	return divd;
}

map polynomial_division(map* divd, map* divr, map* rem)
{
	map quot = NULL;
	Tree* a = NULL;
	if ((*divd)->length < (*divr)->length)
		return polynomial_division(divr, divd, rem);
	while ((*divd)->length >= (*divr)->length)
	{
		a = simplify(join(clone((*divd)->begin->data), clone((*divr)->begin->data), fnc[DIVID].ex));
		*divd = remain(*divr, *divd, a);
		quot = push_back(quot, a);
		(*divd) = pop_front_map(*divd);
		if ((*divd) == NULL)
			break;
		if (iszero(*divd))
		{
			for (int i = 1; i < (*divd)->length - (*divr)->length; ++i)
				quot = push_back(quot, new_tree("0"));
			(*divd) = clear_map(*divd);
			break;
		}
	}
	if ((*divd) == NULL)
		(*divd) = push_back(*divd, new_tree("0"));
	(*divr) = clear_map(*divr);
	*rem = (*divd);
	return quot;
}

map poly_quotient(map u, map v, token tk)
{
	map rem = NULL, coef_u = clone_map(u), coef_v = clone_map(v);
	map L = polynomial_division(&coef_u, &coef_v, &rem);
	if (tk == REMAINDER_F)
	{
		L = clear_map(L);
		return rem;
	}
	rem = clear_map(rem);
	return L;
}

map poly_gcd(map u, map v)
{
	if (u->length == 1 && !strcmp(((Tree*)u->begin->data)->value, "0") && v->length == 1 && !strcmp(((Tree*)v->begin->data)->value, "0"))
		return push_back(NULL, new_tree("1"));
	if (v->length == 1 && u->length == 1)
		return push_back(NULL, PGCD(clone(u->begin->data), clone(v->begin->data)));
	bool k = v->length > u->length;
	map U = k ? clone_map(v) : clone_map(u);
	map V = k ? clone_map(u) : clone_map(v);
	while (strcmp(((Tree*)V->begin->data)->value, "0"))
	{
		map R = poly_quotient(U, V, REMAINDER_F);
		U = clear_map(U);
		U = V;
		V = R;
	}
	V = clear_map(V);
	if (U->length > 1)
	{
		Tree* lcr = clone(U->begin->data);
		mapCell* tmp = U->begin;
		while (tmp != NULL)
		{
			tmp->data = simplify(join(tmp->data, clone(lcr), fnc[DIVID].ex));
			tmp = tmp->next;
		}
		clean_tree(lcr);
	}
	return U;
}

Tree* poly_simp(map u, map v, const char* x)
{
	map pgcd = poly_gcd(u, v);
	if (pgcd->length > 1 || (pgcd->length == 1 && strcmp(((Tree*)pgcd->begin->data)->value, "1")))
	{
		map qn = poly_quotient(u, pgcd, INT_F), qd = poly_quotient(v, pgcd, INT_F);
		pgcd = clear_map(pgcd); u = clear_map(u); v = clear_map(v);
		Tree* n = polyreconstitute(&qn, x), * d = polyreconstitute(&qd, x);
		if (!strcmp(d->value, "1"))
		{
			clean_tree(d);
			return n;
		}
		return join(n, d, fnc[DIVID].ex);
	}
	pgcd = clear_map(pgcd);
	return join(polyreconstitute(&u, x), polyreconstitute(&v, x), fnc[DIVID].ex);
}

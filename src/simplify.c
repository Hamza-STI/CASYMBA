#include "simplify.h"


bool ALG_EXPAND = false;
bool LN_EXP_EXPAND = false;
bool TRIG_EXPAND = false;
bool RT_SIMP = false;
//bool TRIGO_EXACT_SEARCH = false;

static const struct Trigo_value Exact_Values[AMONT_VALUE_TRIG] =
{
	/* remarquables */
	{ "0", "1", "0", "0"},
	{ "1/6*PI", "sqrt(3)/2", "1/2", "sqrt(3)/3" },
	{ "1/4*PI", "sqrt(2)/2", "sqrt(2)/2", "1" },
	{ "1/3*PI", "1/2", "sqrt(3)/2", "sqrt(3)" },
	{ "1/2*PI", "1", "0", "undef" },
	{ "2/3*PI", "~1/2", "sqrt(3)/2", "~sqrt(3)"},
	{ "3/4*PI", "~sqrt(2)/2", "sqrt(2)/2", "~1" },
	{ "5/6*PI", "~sqrt(3)/2", "1/2", "~sqrt(3)/3" },
	{ "PI", "~1", "0", "0" },

	/* moins-remarquables */
	{ "1/12*PI", "sqrt(2+sqrt(3))/2", "sqrt(2-sqrt(3))/2", "2-sqrt(3)" },
	{ "1/10*PI", "sqrt(2*(sqrt(5)+5))/4", "(sqrt(5)-1)/4", "sqrt((5-2*sqrt(5))/5)" },
	{ "1/8*PI", "sqrt(2+sqrt(2))/2", "sqrt(2-sqrt(2))/2", "sqrt(2)-1" },
	{ "1/5*PI", "(sqrt(5)+1)/4", "sqrt(~2*(sqrt(5)-5))/4",	"sqrt(5-2*sqrt(5))" },
	{ "3/8*PI", "sqrt(2-sqrt(2))/2", "sqrt(2+sqrt(2))/2", "sqrt(2)+1" },
	{ "5/12*PI", "sqrt(2-sqrt(3))/2", "sqrt(2+sqrt(3))/2", "2+sqrt(3)" }
};

static Tree* fracOp(const char* numerator, const char* denominator);
static Tree* sumOp(const char* left, const char* right);
static Tree* diffOp(const char* left, const char* right);
static Tree* prodOp(const char* left, const char* right);
static Tree* factOp(const char* left);
static Tree* factorn(double val);

static Tree* simplify_RNE(Tree* u);
static Tree* simplify_RNE_rec(Tree* u);
static Tree* simplify_rational_number(Tree* u);
static Tree* simplify_power(Tree* u);
static Tree* simplify_product(map L);
static Tree* simplify_sum(map L);
static Tree* simplify_ln(Tree* u);
static Tree* simplify_exp(Tree* u);
static Tree* trigo_simplify(Tree* u, token tk);
static map simplify_product_rec(map L);
static map simplify_sum_rec(map L);

static Tree* evaluate_power(Tree* bases, Tree* expon);
static Tree* evaluate_add(Tree* left, Tree* right);
static Tree* evaluate_diff(Tree* left, Tree* right);
static Tree* evaluate_prod(Tree* left, Tree* right);
static Tree* evaluate_quotient(Tree* left, Tree* right);

static Tree* construct(const char* op, map li);
static Tree* rationalize_sum(Tree* u, Tree* v, const char* op);
static Tree* contract_exp(Tree* u);
static Tree* contract_ln_rules(Tree* u);
static Tree* contract_ln(Tree* u);
static Tree* expand_exp(Tree* u);
static Tree* expand_ln(Tree* u);

static int free_of(Tree* u, Tree* t);
static map merge_products(map p, map q);
static map adjoin(Tree* s, map p);
static map merge_sums(map p, map q);
static Tree* absolute_value(Tree* u);

static int free_of(Tree* u, Tree* t)
{
	if (tree_compare(u, t))
		return 0;
	else if (isconstant(u))
		return 1;
	else
	{
		int i = 1, k = nb_operand(u);
		while (i <= k)
		{
			if (!free_of(operand(u, i), t))
				return 0;
			i++;
		}
		return 1;
	}
}

int ispoly(Tree* u, const char* vr)
{
	optype op = u->gtype;
	if (op <= VAR)
		return 1;
	token tk = u->tok_type;
	if (tk == NEGATIF)
		return ispoly(u->tleft, vr);
	if (op == FUNCTION)
		return !found_element(u->tleft, vr);
	if (tk == ADD || tk == SUB || tk == PROD)
		return ispoly(u->tleft, vr) && ispoly(u->tright, vr);
	if (tk == DIVID)
		return ispoly(u->tleft, vr) && !found_element(u->tright, vr);
	if (tk == POW)
		return ispoly(u->tleft, vr) && u->tright->gtype == ENT;
	return 0;
}

int is_int(Tree* u)
{
	if (u->gtype == ENT)
		return 1;
	if (u->tok_type == NEGATIF)
		return is_int(u->tleft);
	return 0;
}

bool is_negation(Tree* u)
{
	if (u->tok_type == NEGATIF)
		return !is_negation(u->tleft);
	if (u->tok_type == PROD || u->tok_type == DIVID)
		return is_negation(u->tleft) || is_negation(u->tright);
	return false;
}

bool isdemi(Tree* tr)
{
	return tr->tok_type == DIVID && !strcmp(tr->tleft->value, "1") && !strcmp(tr->tright->value, "2");
}

Tree* pow_transform(Tree* u)
{
	if (u->tok_type == POW)
	{
		if (isdemi(u->tright))
		{
			u->tleft = pow_transform(u->tleft);
			Tree* v = join(clone(u->tleft), NULL, fnc[SQRT_F].ex);
			v->parent = u->parent;
			clean_tree(u);
			return v;
		}
		else if (!strcmp(u->tright->value, "1"))
		{
			u->tleft = pow_transform(u->tleft);
			Tree* v = clone(u->tleft);
			v->parent = u->parent;
			clean_tree(u);
			return v;
		}
        else if (u->tright->tok_type == NEGATIF)
		{
			u->tleft = pow_transform(u->tleft);
			Tree* v = clone(u->tleft);
			Tree* w = clone(u->tright->tleft);
			Tree* f = join(new_tree("1"), pow_transform(join(v, w, fnc[POW].ex)), fnc[DIVID].ex);
			f->parent = u->parent;
			clean_tree(u);
			return f;
		}
		return u;
	}
	else
	{
		if (u->gtype == OPERAT)
		{
			u->tleft = pow_transform(u->tleft);
			u->tright = pow_transform(u->tright);
			if (u->tok_type == PROD)
			{
                if (!strcmp(u->tleft->value, "1"))
				{
					Tree* w = clone(u->tright);
					clean_tree(u);
					return w;
				}
				if (!strcmp(u->tright->value, "1"))
				{
					Tree* w = clone(u->tleft);
					clean_tree(u);
					return w;
				}
				if (u->tleft->tok_type == DIVID && !strcmp(u->tleft->tleft->value, "1") && u->tright->tok_type != DIVID)
				{
					Tree* v = clone(u->tleft->tright);
					Tree* w = clone(u->tright);
					clean_tree(u);
					u = join(w, v, fnc[DIVID].ex);
				}
				if (u->tright->tok_type == DIVID && !strcmp(u->tright->tleft->value, "1") && u->tleft->tok_type != DIVID)
				{
					Tree* v = clone(u->tleft);
					Tree* w = clone(u->tright->tright);
					clean_tree(u);
					u = join(v, w, fnc[DIVID].ex);
				}
				if (u->tleft->tok_type == DIVID || u->tright->tok_type == DIVID)
				{
					Tree* a = numerator_fun(u->tleft), * b = denominator_fun(u->tleft);
					Tree* c = numerator_fun(u->tright), * d = denominator_fun(u->tright);
					clean_tree(u);
					u = join(join(a, c, fnc[PROD].ex), join(b, d, fnc[PROD].ex), fnc[DIVID].ex);
				}
                if (u->tleft->tok_type == NEGATIF && !strcmp(u->tleft->tleft->value, "1"))
                {
                    Tree* w = clone(u->tright);
                    clean_tree(u);
                    return join(w, NULL, fnc[NEGATIF].ex);
                }
			}
		}
		else if (u->gtype == FUNCTION || u->gtype == NEGATION)
		{
			u->tleft = pow_transform(u->tleft);
		}
		return u;
	}
}

Tree* numerator_fun(Tree* u)
{
	if (u->tok_type == DIVID)
		return clone(u->tleft);
	if (u->tok_type == POW)
	{
		Tree* v = u->tright;
		if (isconstant(v))
		{
			double t = Eval(v);
			if (t < 0)
				return new_tree("1");
		}
	}
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
	if (u->tok_type == POW)
	{
		Tree* v = u->tright;
		if (isconstant(v))
		{
			double t = Eval(v);
			if (t < 0)
				return simplify(join(clone(u), join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex));
			return new_tree("1");
		}
	}
	else if (u->tok_type == NEGATIF)
		return denominator_fun(u->tleft);
	if (u->tok_type == PROD)
		return simplify(join(denominator_fun(u->tleft), denominator_fun(u->tright), fnc[PROD].ex));
	return new_tree("1");
}

Tree* base(Tree* u)
{
	if (u->tok_type == POW)
		return u->tleft;
	return u;
}

Tree* exponent(Tree* u)
{
	if (u->tok_type == POW)
		return clone(u->tright);
	return new_tree("1");
}

Tree* constant(Tree* u)
{
	token tk = u->tok_type;
	if (tk == POW || tk == ADD || tk == SUB || u->gtype == VAR || u->gtype == FUNCTION)
		return new_tree("1");
	if (isconstant(u))
		return u;
	map Li = map_create_prod(u);
	mapCell* tmp_Li = Li->begin;
	Tree* s = NULL;
	while (isconstant(tmp_Li->tr))
	{
		s = (s == NULL) ? clone(tmp_Li->tr) : join(s, clone(tmp_Li->tr), fnc[PROD].ex);
		tmp_Li = tmp_Li->next;
	}
	Li = clear_map(Li);
	return (s != NULL) ? s : new_tree("1");
}

Tree* term(Tree* u)
{
	token tk = u->tok_type;
	if (tk == POW || tk == ADD || tk == SUB || u->gtype == VAR || u->gtype == FUNCTION)
		return clone(u);
	if (isconstant(u))
		return NULL;
	map Li = map_create_prod(u);
	while (isconstant(Li->begin->tr))
		Li = pop_front_map(Li);
	return (Li == NULL)? NULL: construct(fnc[PROD].ex, Li);
}

double factoriel(double a)
{
	double s = 1, i;
	for (i = 1; i <= a; i++)
		s *= i;
	return s;
}

double combinaison(double n, double k)
{
	return factoriel(n) / (factoriel(k) * factoriel(n - k));
}

double fpart(double ex)
{
	return (double)(ex - ((int)ex));
}

Tree* expand_product(Tree* r, Tree* s)
{
	if (r->tok_type == ADD || r->tok_type == SUB)
		return join(simplify(expand_product(r->tleft, s)), simplify(expand_product(r->tright, s)), r->value);
	else if (s->tok_type == ADD || s->tok_type == SUB)
		return expand_product(s, r);
	return join(clone(r), clone(s), fnc[PROD].ex);
}

Tree* expand_power(Tree* u, double n)
{
	if (u->tok_type == ADD || u->tok_type == SUB)
	{
		Tree* f = u->tleft;
		Tree* r = u->tright;
		Tree* s = NULL;
		double c;
		int i;
		for (i = 0; i <= n; i++)
		{
			Tree* g = join(clone(f), new_tree(tostr(n - i)), fnc[POW].ex);
			c = factoriel(n) / (factoriel(i) * factoriel(n - i));
			Tree* a = simplify(join(new_tree(tostr(c)), g, fnc[PROD].ex));
			Tree* b = simplify(expand_power(r, i));
			if (s == NULL)
			{
				s = expand_product(a, b);
			}
			else
			{
				Tree* t = expand_product(a, b);
				s = join(s, t, u->value);
			}
			clean_tree(a);
			clean_tree(b);
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
		Tree* tr1 = expand(tr->tleft);
		Tree* tr2 = expand(tr->tright);
		Tree* t = expand_product(tr1, tr2);
		clean_tree(tr1);
		clean_tree(tr2);
		return t;
	}
	else if (tk == POW)
	{
		Tree* u = expand(tr->tleft);
		Tree* v = tr->tright;
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

Tree* expand_main_op(Tree* u)
{
	if (u->tok_type == PROD || u->tok_type == POW)
	{
		Tree* r = u->tleft;
		Tree* s = u->tright;
		if (r->tok_type == ADD || r->tok_type == SUB)
		{
			map L = map_create(r);
			mapCell* tmp = L->begin;
			Tree* tr = NULL;
			while (tmp != NULL)
			{
				tr = (!tr) ? clone(tmp->tr) : join(tr, clone(tmp->tr), u->value);
				tmp = tmp->next;
			}
			L = clear_map(L);
			return tr;
		}
		else if (u->tok_type == PROD && (s->tok_type == ADD || s->tok_type == SUB))
		{
			Tree* p = join(clone(s), clone(r), fnc[PROD].ex);
			Tree* t = expand_main_op(p);
			clean_tree(p);
			return t;
		}
	}
	return clone(u);
}

int ordre_tree(Tree* u, Tree* v)
{
	if (isconstant(u) && isconstant(v))
		return Eval(u) < Eval(v);
	else if (u->gtype == VAR && v->gtype == VAR)
	{
		string p = u->value, q = v->value;
		int a = strlen(p), b = strlen(q), k = 0;
		int i = (a >= b) ? a : b;
		while (k < i && p[k] == q[k])
			k++;
		return k < i && p[k] < q[k];
	}
	else if (v->gtype == FUNCTION && u->gtype == VAR)
		return 1;
	else if (u->tok_type == v->tok_type && (u->tok_type == ADD || u->tok_type == PROD))
	{
		map p = map_create(u);
		map q = map_create(v);
		if (!tree_compare(p->end->tr, q->end->tr))
		{
			int k = ordre_tree(p->end->tr, q->end->tr);
			p = clear_map(p);
			q = clear_map(q);
			return k;
		}
		else
		{
			mapCell* tmp = p->end;
			mapCell* tmp1 = q->end;
			while (tmp != NULL && tmp1 != NULL)
			{
				if (!tree_compare(tmp->tr, tmp1->tr))
				{
					int k = ordre_tree(tmp->tr, tmp1->tr);
					p = clear_map(p);
					q = clear_map(q);
					return k;
				}
				tmp = tmp->back;
				tmp1 = tmp1->back;
			}
			if (tmp == NULL || tmp1 == NULL)
			{
				int k = p->length < q->length;
				p = clear_map(p);
				q = clear_map(q);
				return k;
			}
		}
		p = clear_map(p);
		q = clear_map(q);
	}
	else if (u->tok_type == v->tok_type && u->tok_type == POW)
		return (!tree_compare(u->tleft, v->tleft)) ? ordre_tree(u->tleft, v->tleft) : ordre_tree(u->tright, v->tright);
	else if (u->tok_type == v->tok_type && u->tok_type == FACTORIEL_F)
		return ordre_tree(u->tleft, v->tleft);
	else if (u->gtype == FUNCTION && v->gtype == FUNCTION)
	{
		if (u->tok_type != v->tok_type)
		{
			string p = u->value, q = v->value;
			int a = strlen(p), b = strlen(q);
			int i = (a >= b) ? a : b;
			int k = 0;
			while (k < i && p[k] == q[k])
				k++;
			return k < i&& p[k] < q[k];
		}
		else
		{
			map p = map_create(u->tleft);
			map q = map_create(v->tleft);
			if (!tree_compare(p->begin->tr, q->begin->tr))
			{
				int k = ordre_tree(p->begin->tr, q->begin->tr);
				p = clear_map(p);
				q = clear_map(q);
				return k;
			}
			else
			{
				mapCell* tmp = p->begin;
				mapCell* tmp1 = q->begin;
				while (tmp != NULL || tmp1 != NULL)
				{
					if (!tree_compare(tmp->tr, tmp1->tr))
					{
						int k = ordre_tree(tmp->tr, tmp1->tr);
						p = clear_map(p);
						q = clear_map(q);
						return k;
					}
					tmp = tmp->next;
					tmp1 = tmp1->next;
				}
				if (!tmp)
				{
					int k = p->length < q->length;
					p = clear_map(p);
					q = clear_map(q);
					return k;
				}
			}
			p = clear_map(p);
			q = clear_map(q);
		}
	}
	else if (isconstant(u) && !isconstant(v))
		return 1;
	else if (u->tok_type == PROD && (v->tok_type == POW || v->tok_type == ADD || v->gtype == FUNCTION || v->gtype == VAR))
	{
		Tree* tr = join(new_tree("1"), clone(v), fnc[PROD].ex);
		int k = ordre_tree(u, tr);
		clean_tree(tr);
		return k;
	}
	else if (u->tok_type == ADD && (v->gtype == FUNCTION || v->gtype == VAR))
	{
		Tree* tr = join(new_tree("0"), clone(v), fnc[ADD].ex);
		int k = ordre_tree(u, tr);
		clean_tree(tr);
		return k;
	}
	else if ((u->tok_type == FACTORIEL_F && (v->gtype == FUNCTION && v->tok_type != FACTORIEL_F)) || v->gtype == VAR)
		return ordre_tree(u->tleft, v);
	else if (u->tok_type == POW && v->tok_type != POW)
	{
		Tree* tr = join(clone(v), new_tree("1"), fnc[POW].ex);
		int k = !ordre_tree(tr, u);
		clean_tree(tr);
		return k;
	}
	else if (u->tok_type != POW && v->tok_type == POW)
	{
		Tree* tr = join(clone(u), new_tree("1"), fnc[POW].ex);
		int k = !ordre_tree(v, tr);
		clean_tree(tr);
		return k;
	}
	return 0;
}

map map_sort(map li)
{
	mapCell* tmp = li->begin;
	while (tmp != NULL)
	{
		mapCell* tmp1 = li->begin;
		while (tmp1 != NULL)
		{
			if (ordre_tree(tmp->tr, tmp1->tr))
			{
				Tree* t = clone(tmp1->tr), * s = clone(tmp->tr);
				clean_tree(tmp1->tr); clean_tree(tmp->tr);
				tmp1->tr = s; tmp->tr = t;
			}
			tmp1 = tmp1->next;
		}
		tmp = tmp->next;
	}
	return li;
}

Tree* trigo_identify(const char* s, token tk)
{
	const Trigo_value* element;
	int k = 0;
	for (element = Exact_Values; element != element + AMONT_VALUE_TRIG; element++)
	{
		if (tk == COS_F || tk == SIN_F || tk == TAN_F)
		{
			if (!strcmp(s, element->angle))
			{
				if (tk == COS_F)
					return to_tree(In2post2(element->cos_value));
				if (tk == SIN_F)
					return to_tree(In2post2(element->sin_value));
				if (tk == TAN_F)
					return to_tree(In2post2(element->tan_value));
			}
		}
		else
		{
			if (!strcmp(s, element->cos_value) ||!strcmp(s, element->sin_value) || !strcmp(s, element->tan_value))
				return to_tree(In2post2(element->angle));
		}
		k++;
		if (k == AMONT_VALUE_TRIG)
			return NULL;
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

static Tree* simplify_rational_number(Tree* u)
{
	if (count_tree_nodes(u) == 3 && u->tok_type == DIVID)
	{
		Tree* n = u->tleft;
		Tree* d = u->tright;
		int a = atoi(n->value), b = atoi(d->value);
		if (!(a % b))
		{
			return new_tree(tostr(iquot(a, b)));
		}
		else
		{
			int g = integer_gcd(a, b);
			a = iquot(a, g);
			b = iquot(b, g);
			if (g != 1)
				return join(new_tree(tostr(a)), new_tree(tostr(b)), fnc[DIVID].ex);
		}
	}
	return clone(u);
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
		else
		{
			Tree* t = simplify_rational_number(u);
			clean_tree(u);
			return t;
		}
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
		if (t->gtype == ENT)
		{
			Tree* ret = factOp(t->value);
			clean_tree(t);
			clean_noeud(u);
			return ret;
		}
		clean_tree(u);
		clean_tree(t);
		return new_tree(fnc[UNDEF].ex);
	}
	else if (u->tok_type == ABS_F)
	{
		double d = Eval(u->tleft);
		if (d < 0)
		{
			Tree* t = simplify_RNE_rec(join(u->tleft, join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[PROD].ex));
			clean_noeud(u);
			return t;
		}
		Tree* tr = clone(u->tleft);
		clean_tree(u);
		return tr;
	}
	else
	{
		Tree* v = simplify_RNE(u->tleft);
		Tree* w = simplify_RNE(u->tright);
		if (v->tok_type == UNDEF || w->tok_type == UNDEF)
		{
			clean_tree(u);
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
			clean_noeud(u);
			return tr;
		}
	}
}

static Tree* evaluate_quotient(Tree* left, Tree* right)
{
	Tree* t = numerator_fun(right);
	if (!strcmp(t->value, "0"))
	{
		clean_tree(t);
		return new_tree(fnc[UNDEF].ex);
	}
	clean_tree(t);
	Tree* i = simplify_RNE_rec(join((numerator_fun(left)), (denominator_fun(right)), fnc[PROD].ex));
	Tree* j = simplify_RNE_rec(join((numerator_fun(right)), (denominator_fun(left)), fnc[PROD].ex));
	int k = count_tree_nodes(i), l = count_tree_nodes(j);
	Tree* tr = NULL;
	if (k == 1 && l == 1)
		tr = fracOp(i->value, j->value);
	else if (k == 2 && l == 1 && i->tok_type == NEGATIF)
		tr = join(fracOp(i->tleft->value, j->value), NULL, fnc[NEGATIF].ex);
	else if (l == 2 && k == 1 && j->tok_type == NEGATIF)
		tr = join(fracOp(i->value, j->tleft->value), NULL, fnc[NEGATIF].ex);
	else if (k == 2 && k == l && j->tok_type == NEGATIF && j->tok_type == i->tok_type)
		tr = fracOp(i->tleft->value, j->tleft->value);
	else
		tr = join(clone(i), clone(j), fnc[DIVID].ex);
	clean_tree(i);
	clean_tree(j);
	return tr;
}

static Tree* evaluate_power(Tree* bases, Tree* expon)
{
	double e = Eval(expon);
	Tree* tr = numerator_fun(bases);
	if (strcmp(tr->value, "0"))
	{
		clean_tree(tr);
		if (!strcmp(expon->value, "0"))
			return new_tree("1");
		if (!strcmp(expon->value, "1"))
			return clone(bases);
		Tree* v = denominator_fun(bases);
		if (!strcmp(v->value, "1"))
		{
			clean_tree(v);
			if (e > 0)
			{
                if (expon->gtype == ENT)
                {
                    if (bases->gtype == ENT)
                    {
                        int c = round(pow((int)tonumber(bases->value), (int)tonumber(expon->value)));
                        return new_tree(tostr(c));
                    }
                    if (is_int(bases))
                    {
                        v = evaluate_power(bases->tleft, expon);
                        e = (int)e;
                        if ((e / 2) != (int)(e / 2))
                            v = join(v, NULL, fnc[NEGATIF].ex);
                        return v;
                    }
                }
				Tree* r = join(bases, expon, fnc[POW].ex);
				e = Eval(r);
				clean_noeud(r);
				if (e < 0)
					return join(new_tree(tostr(-e)), NULL, fnc[NEGATIF].ex);
				return new_tree(tostr(e));
			}
			else
			{
				Tree* r = new_tree("1"), * s = evaluate_power(bases, expon->tleft);
				Tree* t = evaluate_quotient(r, s);
				clean_tree(r); clean_tree(s);
				return t;
			}
		}
		else
		{
			Tree* u = numerator_fun(bases);
			if (e > 0)
			{
				Tree* r = join(u, clone(expon), fnc[POW].ex);
				Tree* s = join(v, clone(expon), fnc[POW].ex);
				double f = Eval(s);
				e = Eval(r);
				clean_tree(s);
				clean_tree(r);
				return join(new_tree(tostr(e)), new_tree(tostr(f)), fnc[DIVID].ex);
			}
			Tree* r = evaluate_power(v, expon->tleft);
			Tree* s = evaluate_power(u, expon->tleft);
			clean_tree(u); clean_tree(v);
			u = evaluate_quotient(r, s);
			clean_tree(r); clean_tree(s);
			return u;
		}
	}
	else
	{
		clean_tree(tr);
		if (e < 0)
			return new_tree(fnc[UNDEF].ex);
		return new_tree("0");
	}
}

static Tree* evaluate_add(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0"))
		return clone(right);
	if (!strcmp(right->value, "0"))
		return clone(left);
	if (count_tree_nodes(left) == 1 && count_tree_nodes(right) == 1)
    {
        if (left->gtype == ENT && right->gtype == ENT)
            return new_tree(tostr((int)tonumber(left->value) + (int)tonumber(right->value)));
        return sumOp(left->value, right->value);
    }
	else if (left->tok_type == NEGATIF)
		return evaluate_diff(right, left->tleft);
	else if (right->tok_type == NEGATIF)
		return evaluate_diff(left, right->tleft);
	else
	{
		Tree* u = numerator_fun(left), * v = denominator_fun(left);
		Tree* w = numerator_fun(right), * x = denominator_fun(right);
		Tree* xx = clone(x);
		Tree* vv = clone(v);
		Tree* num1 = simplify_RNE_rec(join(u, x, fnc[PROD].ex));
		Tree* num2 = simplify_RNE_rec(join(v, w, fnc[PROD].ex));
		Tree* denom = simplify_RNE_rec(join(vv, xx, fnc[PROD].ex));
		Tree* num = simplify_RNE_rec(join(num1, num2, fnc[ADD].ex));
		Tree* t = join(num, denom, fnc[DIVID].ex);
		return simplify_RNE_rec(t);
	}
}

static Tree* evaluate_diff(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0"))
		return clone(right);
	if (!strcmp(right->value, "0"))
		return clone(left);
	if (count_tree_nodes(left) == 1 && count_tree_nodes(right) == 1)
		return diffOp(left->value, right->value);
	else if (left->tok_type == NEGATIF && right->tok_type == NEGATIF)
		return evaluate_diff(right->tleft, left->tleft);
	else if (left->tok_type == NEGATIF)
		return join(evaluate_add(left->tleft, right), NULL, fnc[NEGATIF].ex);
	else if (right->tok_type == NEGATIF)
		return evaluate_add(left, right->tleft);
	else
	{
		Tree* u = numerator_fun(left), * v = denominator_fun(left);
		Tree* w = numerator_fun(right), * x = denominator_fun(right);
		Tree* xx = clone(x), * vv = clone(v);
		Tree* num1 = simplify_RNE_rec(join(u, x, fnc[PROD].ex));
		Tree* num2 = simplify_RNE_rec(join(v, w, fnc[PROD].ex));
		Tree* denom = simplify_RNE_rec(join(vv, xx, fnc[PROD].ex));
		Tree* num = simplify_RNE_rec(join(num1, num2, fnc[SUB].ex));
		if (num->tok_type != NEGATIF)
		{
			Tree* t = join(num, denom, fnc[DIVID].ex);
			return simplify_RNE_rec(t);
		}
		else
		{
			Tree* t = join(num->tleft, denom, fnc[DIVID].ex);
			Tree* tr = join(simplify_RNE_rec(t), NULL, fnc[NEGATIF].ex);
			clean_noeud(num);
			return tr;
		}
	}
}

static Tree* evaluate_prod(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0") || !strcmp(right->value, "0"))
		return new_tree("0");
	if (count_tree_nodes(left) == 1 && count_tree_nodes(right) == 1)
		return prodOp(left->value, right->value);
	else if (left->tok_type == NEGATIF && right->tok_type == NEGATIF)
		return evaluate_prod(left->tleft, right->tleft);
	else if (left->tok_type == NEGATIF)
		return join(simplify_RNE_rec(join(clone(right), clone(left->tleft), fnc[PROD].ex)), NULL, fnc[NEGATIF].ex);
	else if (right->tok_type == NEGATIF)
		return join(simplify_RNE_rec(join(clone(left), clone(right->tleft), fnc[PROD].ex)), NULL, fnc[NEGATIF].ex);
	else
	{
		Tree* u = (numerator_fun(left));
		Tree* v = (denominator_fun(left));
		Tree* w = (numerator_fun(right));
		Tree* x = (denominator_fun(right));
		Tree* num = simplify_RNE_rec(join(u, w, fnc[PROD].ex));
		Tree* denom = simplify_RNE_rec(join(v, x, fnc[PROD].ex));
		Tree* ret = join(num, denom, fnc[DIVID].ex);
		return simplify_RNE_rec(ret);
	}
}

static Tree* fracOp(const char* numerator, const char* denominator)
{
	double num = tonumber(numerator);
	double denom = tonumber(denominator);
	string in = strchr(numerator, '.');
	string id = strchr(denominator, '.');
	if (in == NULL && id == NULL)
	{
		int pgcd = integer_gcd(num, denom);
		num /= pgcd;
		denom /= pgcd;
		if (denom == 1)
			return new_tree(tostr(num));
		return join(new_tree(tostr(num)), new_tree(tostr(denom)), fnc[DIVID].ex);
	}
	return new_tree(tostr(num / denom));
}

static Tree* sumOp(const char* left, const char* right)
{
	return new_tree(tostr(tonumber(left) + tonumber(right)));
}

static Tree* diffOp(const char* left, const char* right)
{
	double t = tonumber(left) - tonumber(right);
	if (t < 0)
		return join(new_tree(tostr(-t)), NULL, fnc[NEGATIF].ex);
	if (t == 0)
		return new_tree("0");
	return new_tree(tostr(t));
}

static Tree* prodOp(const char* left, const char* right)
{
	return new_tree(tostr(tonumber(left) * tonumber(right)));
}

static Tree* factOp(const char* left)
{
	double n = tonumber(left);
	string in = strchr(left, '.');
	if (!in)
	{
		double s = factoriel(n);
		return new_tree(tostr(s));
	}
	return new_tree(fnc[UNDEF].ex);
}

int integer_gcd(int a, int b)
{
	int r = (int)a % (int)b;
	while (r)
	{
		a = b;
		b = r;
		r = (int)a % (int)b;
	}
	return b;
}

static Tree* factorn(double val)
{
	Tree* tr = NULL;
	int f = 2, e = 0;
	double m = sqrt(val);
	double fractpart;
	while (f <= m)
	{
		fractpart = fpart(val / f);
		while (fractpart == 0)
		{
			e++;
			val /= f;
			fractpart = fpart(val / f);
		}
		if (e > 0)
		{
			if (tr != NULL)
				tr = join(tr, (e == 1) ? new_tree(tostr((double)f)) : join(new_tree(tostr((double)f)), new_tree(tostr((double)e)), fnc[POW].ex), fnc[PROD].ex);
			else
				tr = (e == 1) ? new_tree(tostr((double)f)) : join(new_tree(tostr((double)f)), new_tree(tostr((double)e)), fnc[POW].ex);
			e = 0;
			m = sqrt(val);
		}
		f = (f == 2) ? 3 : f + 2;
	}
	if (val != 1)
	{
		if (tr != NULL)
			tr = join(tr, new_tree(tostr((double)f)), fnc[PROD].ex);
		else
			tr = new_tree(tostr((double)f));
	}
	return tr;
}

Tree* texpand(Tree* f, token tk)
{
	if (f->tok_type == ADD || f->tok_type == SUB)
	{
		Tree* a = f->tleft, * b = f->tright;
		token tk1 = (tk == COS_F) ? SIN_F : COS_F, op_tk = f->tok_type;
		Tree* v = texpand(a, tk), * w = texpand(b, tk1);
		Tree* p = texpand(b, tk), * q = texpand(a, tk1);
		if (tk == COS_F)
		{
			op_tk = (f->tok_type == ADD) ? SUB : ADD;
			return join(join(v, p, fnc[PROD].ex), join(w, q, fnc[PROD].ex), fnc[op_tk].ex);
		}
        if(op_tk == SUB)
        {
            return join(join(q, p, fnc[PROD].ex), join(v, w, fnc[PROD].ex), fnc[op_tk].ex);
        }
		return join(join(v, w, fnc[PROD].ex), join(q, p, fnc[PROD].ex), fnc[op_tk].ex);
	}
	return trigo_simplify(clone(f), tk);
}

Tree* trigo_simplify(Tree* u, token tk)
{
	if (tk == COS_F && is_negation(u))
	{
		u = simplify(join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), u, fnc[PROD].ex));
		return trigo_simplify(u, tk);
	}
	if (tk == SIN_F && is_negation(u))
	{
		u = simplify(join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), u, fnc[PROD].ex));
		return simplify(join(trigo_simplify(u, tk), NULL, fnc[NEGATIF].ex));
	}
	string su = Post2in2(u);
    Tree* s = trigo_identify(su, tk);
    if (s != NULL)
    {
        clean_tree(u);
        return s;
    }
	if (found_element(u, fnc[PI].ex) && (tk == COS_F || tk == SIN_F))
    {
        Tree* o = new_tree("1");
        Tree* c = coefficient_gpe(u, fnc[PI].ex, o);
        double e = Eval(c);
        clean_tree(o);
        if (fabs(e) > 3.14)
        {
            Tree* cst = NULL;
            o = new_tree("2");
            cst = simplify(join(PGCD(c, o), new_tree("1"), fnc[SUB].ex));
            clean_tree(o);
            if (cst->tok_type == NEGATIF)
            {
                clean_tree(u);
                cst = join(cst, new_tree(fnc[PI].ex), fnc[PROD].ex);
                return trigo_simplify(cst, tk);
            }
            clean_tree(c);
            c = cst;
        }
        Tree* tmp = join(clone(c), new_tree(fnc[PI].ex), fnc[PROD].ex);
		string tmps = Post2in2(tmp);
        Tree* s = trigo_identify(tmps, tk);
        clean_tree(tmp);
        if (s != NULL)
        {
            clean_tree(c); clean_tree(u);
            return s;
        }
		clean_tree(c);
        /*char ls[8][2] = { "2", "3", "4", "5", "6", "8", "10", "12" };
        int li[] = { 2, 3, 4, 5, 6, 8, 10, 12 }, y[2] = { 0, 0 }, index_y[2] = { 0, 0 };
        double v = 0;
        bool b = false;
        Tree* n = numerator_fun(c), * d = denominator_fun(c);
        int z = (int)Eval(n), r = (int)Eval(d), w = 0;
        clean_tree(c);
        for (int i = 7; i >= 0; i--)
        {
            if (!strcmp(d->value, ls[i]) && is_int(n))
            {
                clean_tree(u);
                c = join(new_tree("1"), clone(d), fnc[DIVID].ex);
                if (n->tok_type == NEGATIF)
                    c = join(c, NULL, fnc[NEGATIF].ex);
                tmp = join(clone(c), new_tree(fnc[PI].ex), fnc[PROD].ex);
                for (int k = 1; k < abs(z); k++)
                    tmp = join(tmp, join(clone(c), new_tree(fnc[PI].ex), fnc[PROD].ex), fnc[ADD].ex);
                clean_tree(n); clean_tree(d); clean_tree(c);
                u = texpand(tmp, tk);
                clean_tree(tmp);
                return u;
            }
            if (w < 2)
            {
                v = (double)r / li[i];
                if (v == (int)v)
                {
                    y[w] = li[i];
                    index_y[w] = i;
                    if (w == 1)
                    {
                        v = (double)y[0] * y[1] / r;
                        if (v == (int)v)
                        {
                            b = true;
                            break;
                        }
                        else
                        {
                            w = 0;
                            y[w] = li[i];
                            index_y[w] = i;
                        }
                    }
                    w++;
                }
            }
        }
        if (b)
        {
            clean_tree(n); clean_tree(d); n = NULL;
            for (int i = 1; i < y[0]; i++)
            {
                for (int k = 1; k < y[1]; k++)
                {
                    w = (int)(i * y[0] - k * y[1]);
                    if (w == (int)v || w == 1)
                    {
                        clean_tree(u);
                        tmp = join(join(new_tree(tostr(i)), new_tree(ls[index_y[0]]), fnc[DIVID].ex), new_tree(fnc[PI].ex), fnc[PROD].ex);
                        tmp = join(tmp, join(join(new_tree(tostr(k)), new_tree(ls[index_y[1]]), fnc[DIVID].ex), new_tree(fnc[PI].ex), fnc[PROD].ex), fnc[SUB].ex);
                        for (int j = z; j > 0; j--)
                        {
                            n = (n == NULL)? clone(tmp) : join(n, clone(tmp), fnc[ADD].ex);
                        }
                        clean_tree(tmp);
                        u = texpand(n, tk);
                        clean_tree(n);
                        return u;
                    }
                    w = (int)(k * y[1] - i * y[0]);
                    if (w == (int)v || w == 1)
                    {
                        clean_tree(u);
                        tmp = join(join(new_tree(tostr(k)), new_tree(ls[index_y[1]]), fnc[DIVID].ex), new_tree(fnc[PI].ex), fnc[PROD].ex);
                        tmp = join(join(join(new_tree(tostr(i)), new_tree(ls[index_y[0]]), fnc[DIVID].ex), new_tree(fnc[PI].ex), fnc[PROD].ex), tmp, fnc[SUB].ex);
                        for (int j = z; j > 0; j--)
                        {
                            n = (n == NULL)? clone(tmp) : join(n, clone(tmp), fnc[ADD].ex);
                        }
                        clean_tree(tmp);
                        u = texpand(n, tk);
                        clean_tree(n);
                        return u;
                    }
                    w = (int)(i * y[0] + k * y[1]);
                    if (w == (int)v || w == 1)
                    {
                        clean_tree(u);
                        tmp = join(join(new_tree(tostr(z)), new_tree(ls[index_y[0]]), fnc[DIVID].ex), new_tree(fnc[PI].ex), fnc[PROD].ex);
                        tmp = join(tmp, join(join(new_tree(tostr(z)), new_tree(ls[index_y[1]]), fnc[DIVID].ex), new_tree(fnc[PI].ex), fnc[PROD].ex), fnc[ADD].ex);
                        for (int j = z; j > 0; j--)
                        {
                            n = (n == NULL)? clone(tmp) : join(n, clone(tmp), fnc[ADD].ex);
                        }
                        clean_tree(tmp);
                        u = texpand(n, tk);
                        clean_tree(n);
                        return u;
                    }
                }
            }
        }
        else
        {
            clean_tree(n);
            clean_tree(d);
        }*/
    }
	return join(u, NULL, fnc[tk].ex);
}

/* symbolic simplify */

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
            if (q > 0)
                return new_tree("1");
            return join(new_tree("1"), NULL, fnc[NEGATIF].ex);
        }
        Tree* r = clone(u);
        clean_tree(u);
        return r;
    }
    if (tk == SQRT_F)
	{
		if (u->tleft->tok_type == NEGATIF && isconstant(u->tleft))
		{
			Tree* tr = simplify(join(u->tleft->tleft, join(new_tree("1"), new_tree("2"), fnc[DIVID].ex), fnc[POW].ex));
			clean_noeud(u->tleft);
			clean_noeud(u);
			return join(tr, new_tree(fnc[IMAGE].ex), fnc[PROD].ex);
		}
		Tree* tr = simplify(join(u->tleft, join(new_tree("1"), new_tree("2"), fnc[DIVID].ex), fnc[POW].ex));
		clean_noeud(u);
		return tr;
	}
	if (tk == NEGATIF)
	{
		Tree* tr = simplify(join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), u->tleft, fnc[PROD].ex));
		clean_noeud(u);
		return tr;
	}
	if (tk == EXP_F)
	{
		u->tleft = simplify(u->tleft);
		Tree* t = simplify_exp(u);
		clean_tree(u);
		return t;
	}
	if (tk == LN_F)
	{
		u->tleft = simplify(u->tleft);
		Tree* t = simplify_ln(u);
		clean_tree(u);
		return t;
	}
	if (tk == LOGBASE_F || tk == LOG_F)
	{
		if (u->tleft->tok_type == SEPARATEUR)
		{
			u->tleft->tleft = simplify(u->tleft->tleft);
			u->tleft->tright = simplify(u->tleft->tright);
			Tree* v = join(clone(u->tleft->tleft), NULL, fnc[LN_F].ex);
			Tree* w = join(clone(u->tleft->tright), NULL, fnc[LN_F].ex);
			clean_tree(u);
			v = simplify_ln(v);
			w = simplify_ln(w);
			if (v->tok_type == UNDEF || w->tok_type == UNDEF)
			{
				clean_tree(v); clean_tree(w);
				return new_tree(fnc[UNDEF].ex);
			}
			return join(v, join(w, join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex), fnc[PROD].ex);
		}
		u->tleft = simplify(u->tleft);
		clean_noeud(u);
		u = join(u, NULL, fnc[LN_F].ex);
		Tree* v = simplify_ln(u), * w = join(new_tree("10"), NULL, fnc[LN_F].ex);
		clean_tree(u);
		return join(v, join(w, join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex), fnc[PROD].ex);
	}
	if (tk == ABS_F)
	{
		Tree* t = absolute_value(simplify(u->tleft));
		clean_noeud(u);
		return t;
	}
    if (tk == COS_F || tk == SIN_F || tk == ACOS_F || tk == ASIN_F)
	{
		u->tleft = simplify(u->tleft);
		Tree* r = trigo_simplify(u->tleft, tk);
		clean_noeud(u);
		return r;
	}
	if (tk == TAN_F)
	{
		u->tleft = simplify(u->tleft);
		Tree* v = join(clone(u->tleft), NULL, fnc[SIN_F].ex);
		Tree* w = join(join(clone(u->tleft), NULL, fnc[COS_F].ex), join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex);
		clean_tree(u);
		return join(v,w, fnc[PROD].ex);
	}
	if (tk == ROOT_F)
	{
		Tree* tr = u->tleft;
		clean_noeud(u);
		if (tr->tok_type != SEPARATEUR)
			return simplify(join(tr, NULL, fnc[SQRT_F].ex));
		return simplify(join(tr->tleft, join(new_tree("1"), tr->tright, fnc[DIVID].ex), fnc[POW].ex));
	}
	if (EXP_F <= tk && tk < ROOT_F)
	{
		Tree* t = join(simplify(u->tleft), NULL, u->value);
		clean_noeud(u);
		return t;
	}
	if (tk == POW)
		return simplify_power(u);
	if (tk == ADD || tk == SUB || tk == PROD || tk == DIVID)
	{
		if (tk == PROD)
		{
			LN_EXP_EXPAND = false;
			Tree* r = expand(u);
			clean_tree(u);
			u = r;
			tk = u->tok_type;
		}
		bool need_sort = false, cplx = (tk == DIVID && found_element(u->tright, fnc[IMAGE].ex));
		map v = map_create(u);
		clean_tree(u);
		mapCell* tmp = v->begin;
		while (tmp != NULL)
		{
			if (tmp->tr->gtype > VAR)
			{
				tmp->tr = simplify(tmp->tr);
				if ((tk == PROD || tk == DIVID) && tmp->tr->tok_type == PROD)
				{
					map d = map_create_prod(tmp->tr);
					mapCell* k = d->begin->next;
					clean_tree(tmp->tr);
					tmp->tr = clone(d->begin->tr);
					while (k != NULL)
					{
						v = push_back_map(v, k->tr);
						k = k->next;
					}
					d = clear_map(d);
					need_sort = true;
				}
			}
			tmp = tmp->next;
		}
		Tree* ret = NULL;
		if (need_sort)
			v = map_sort(v);
		if (tk == PROD || tk == DIVID)
			ret = simplify_product(v);
		if (tk == ADD || tk == SUB)
			ret = simplify_sum(v);
		if (cplx)
		{
			Tree* tr = pow_transform(ret);
			if (tr->tok_type == DIVID && found_element(tr->tright, fnc[IMAGE].ex))
			{
				Tree* z = new_tree("0"), * o = new_tree("1");
				Tree* r = clone(tr->tright);
				Tree* a = coefficient_gpe(r, fnc[IMAGE].ex, z), * b = coefficient_gpe(r, fnc[IMAGE].ex, o);
				clean_tree(z); clean_tree(o); clean_tree(r);
				z = join(clone(tr->tleft), join(clone(a), join(clone(b), new_tree(fnc[IMAGE].ex), fnc[PROD].ex), fnc[SUB].ex), fnc[PROD].ex);
				o = join(join(a, new_tree("2"), fnc[POW].ex), join(b, new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
				clean_tree(tr);
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

Tree* simplify_integer_power(Tree* v, Tree* w)
{
	if (v->gtype < VAR || (3 == count_tree_nodes(v) && v->tok_type == DIVID && v->tleft->gtype < VAR && v->tright->gtype < VAR))
		return simplify_RNE(join(v, w, fnc[POW].ex));
	else if (!strcmp("0", w->value))
	{
		clean_tree(v);
		clean_tree(w);
		return new_tree("1");
	}
	else if (!strcmp("1", w->value))
	{
		clean_tree(w);
		return v;
	}
	else if (!strcmp("2", w->value) && v->tok_type == SIN_F && TRIG_EXPAND)
	{
		Tree* s = join(new_tree("1"), join(join(v->tleft, NULL, fnc[COS_F].ex), w, fnc[POW].ex), fnc[SUB].ex);
		clean_noeud(v);
		return s;
	}
	else if (v->tok_type == POW)
	{
		Tree* r = v->tleft;
		Tree* s = v->tright;
		clean_noeud(v);
		Tree* p = simplify(join(s, w, fnc[PROD].ex));
		if (p->gtype == ENT)
			return simplify_integer_power(r, p);
		return join(r, p, fnc[POW].ex);
	}
	else if (v->tok_type == PROD)
	{
		map r = map_create_prod(v);
		map l = NULL;
		mapCell* tmp = r->begin;
		clean_tree(v);
		while (tmp != NULL)
		{
			Tree* e = simplify(join(clone(tmp->tr), clone(w), fnc[POW].ex));
			l = push_back_map(l, e);
			clean_tree(e);
			tmp = tmp->next;
		}
		r = clear_map(r);
		clean_tree(w);
		return simplify_product(l);
	}
	else if (v->tok_type == DIVID)
	{
		Tree* n = numerator_fun(v);
		Tree* d = denominator_fun(v);
		Tree* s = simplify(join(n, clone(w), fnc[POW].ex));
		Tree* q = simplify(join(d, join(clone(w), NULL, fnc[NEGATIF].ex), fnc[POW].ex));
		clean_tree(v);
		clean_tree(w);
		if (ordre_tree(q, s))
			return join(q, s, fnc[PROD].ex);
		return join(s, q, fnc[PROD].ex);
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
    if (!strcmp("2", w->value) && v->tok_type == COS_F)
		TRIG_EXPAND = true;
	return join(v, w, fnc[POW].ex);
}

static Tree* simplify_power(Tree* u)
{
	Tree* v = simplify(u->tleft);
	Tree* w = simplify(u->tright);
	clean_noeud(u);
	if (!strcmp(v->value, fnc[UNDEF].ex) || !strcmp(w->value, fnc[UNDEF].ex))
	{
		clean_tree(v);
		clean_tree(w);
		return new_tree(fnc[UNDEF].ex);
	}
	else if (!strcmp(v->value, "0"))
	{
		if (isconstant(w))
		{
			double t = Eval(w);
			clean_tree(v);
			clean_tree(w);
			return (t > 0) ? new_tree("0") : new_tree(fnc[UNDEF].ex);
		}
		return join(v, w, fnc[POW].ex);
	}
	else if (!strcmp(v->value, "1"))
	{
		clean_tree(w);
		return v;
	}
	else if (v->tok_type == EXP_F)
	{
		v->tleft = join(w, v->tleft, fnc[PROD].ex);
		return simplify(v);
	}
	else if (v->tok_type == PROD)
	{
		Tree* v1 = join(clone(v->tleft), clone(w), fnc[POW].ex);
		Tree* v2 = join(clone(v->tright), clone(w), fnc[POW].ex);
		clean_tree(v); clean_tree(w);
		v1 = simplify_power(v1);
		v2 = simplify_power(v2);
		return join(v1, v2, fnc[PROD].ex);
	}
	else if (w->gtype == ENT)
		return simplify_integer_power(v, w);
	else if (w->gtype == NEGATION)
	{
		Tree* tr = simplify(join(v, w->tleft, fnc[POW].ex));
		clean_noeud(w);
		if (tr->tok_type == POW)
		{
			if (isdemi(tr->tright) && tr->tleft->gtype == ENT)
				return join(join(clone(tr->tleft), join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex), tr, fnc[PROD].ex);
			Tree* p = (join(tr->tright, NULL, fnc[NEGATIF].ex));
			Tree* r = join(tr->tleft, simplify(p), fnc[POW].ex);
			clean_noeud(tr);
			return r;
		}
		return join(tr, join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex);
	}
	else if (v->gtype == ENT)
	{
		Tree* f = factorn(tonumber(v->value));
		if (f->tok_type == POW)
		{
			Tree* tr = simplify_integer_power(clone(f), w);
			clean_tree(v);
			clean_tree(f);
			return tr;
		}
		else if (f->tok_type == PROD)
		{
			map L = map_create_prod(f);
			clean_tree(f);
			clean_tree(v);
			Tree* s = new_tree("1");
			Tree* q = NULL;
			mapCell* item = L->begin;
			while (item != NULL)
			{
				if (item->tr->tok_type == POW)
				{
					Tree* k = simplify_integer_power(clone(item->tr), clone(w));
					if (k->gtype == ENT)
						s = simplify(join(s, k, fnc[PROD].ex));
					else if (k->tok_type == PROD)
					{
						s = simplify(join(s, k->tleft, fnc[PROD].ex));
						q = (q == NULL) ? k->tright : join(q, k->tright, fnc[PROD].ex);
						clean_noeud(k);
					}
					else
						q = (q == NULL) ? k : join(q, k, fnc[PROD].ex);
				}
				else
					q = (q == NULL) ? join(clone(item->tr), clone(w), fnc[POW].ex) : join(q, join(clone(item->tr), clone(w), fnc[POW].ex), fnc[PROD].ex);
				item = item->next;
			}
			L = clear_map(L);
			clean_tree(w);
			if (q != NULL)
			{
				RT_SIMP = true;
				s = join(s, Contract_pow(q), fnc[PROD].ex);
			}
			return s;
		}
		clean_tree(f);
		if (w->tok_type == DIVID)
		{
			if (w->tleft->gtype == ENT && w->tright->gtype == ENT)
			{
				int n = (int)tonumber(w->tleft->value), d = (int)tonumber(w->tright->value);
				int q = (int)(n / d), r = (int)(n % d);
				if (q > 0)
				{
					string s = tostr((double)q), p = tostr((double)r);
					Tree* bs = simplify(join(clone(v), new_tree(s), fnc[POW].ex));
					Tree* xp = join(new_tree(p), clone(w->tright), fnc[DIVID].ex);
					clean_tree(w);
					return join(bs, join(v, xp, fnc[POW].ex), fnc[PROD].ex);
				}
			}
		}
	}
	else if (v->tok_type == DIVID)
	{
		Tree* n = numerator_fun(v);
		Tree* d = denominator_fun(v);
		Tree* s = join(n, clone(w), fnc[POW].ex);
		Tree* q = join(d, clone(w), fnc[POW].ex);
		Tree* g = simplify(clone(s));
		Tree* h = simplify(clone(q));
		if (!tree_compare(g, s) || !tree_compare(h, q))
		{
			clean_tree(s); clean_tree(q); clean_tree(v); clean_tree(w);
			if (!strcmp(h->value, "1"))
				return g;
			h = join(h, join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex);
			return join(g, h, fnc[PROD].ex);
		}
		clean_tree(s); clean_tree(q); clean_tree(g); clean_tree(h);
	}
	else if (v->tok_type == POW)
	{
		Tree* r = v->tleft;
		w = simplify(join(v->tright, w, fnc[PROD].ex));
		clean_noeud(v);
		return join(r, w, fnc[POW].ex);
	}
    else if (v->tok_type == NEGATIF && isconstant(v) && w->tok_type == DIVID && !strcmp(w->tright->value, "2"))
	{
		Tree* p = clone(v->tleft), * r = clone(w->tleft);
		clean_tree(v);
		u = simplify_power(join(p, w, fnc[POW].ex));
		Tree* q = new_tree(fnc[IMAGE].ex);
		q = simplify_integer_power(q, r);
		return simplify(join(u, q, fnc[PROD].ex));
	}
	return join(v, w, fnc[POW].ex);
}

static map adjoin(Tree* s, map p)
{
	p = push_front_map(p, s);
	return p;
}

static map merge_products(map p, map q)
{
	if (q == NULL)
		return p;
	if (p == NULL)
		return q;
	Tree* p1 = p->begin->tr;
	Tree* q1 = q->begin->tr;
	map t = NULL;
	t = push_back_map(t, p1);
	t = push_back_map(t, q1);
	map h = simplify_product_rec(t);
	if (h == NULL)
	{
		p = pop_front_map(p);
		q = pop_front_map(q);
		return merge_products(p, q);
	}
	else if (h->length == 1)
	{
		p = pop_front_map(p);
		q = pop_front_map(q);
		map L = merge_products(p, q);
		L = push_front_map(L, h->begin->tr);
		h = clear_map(h);
		return L;
	}
	else if (tree_compare(h->begin->tr, p1))
	{
		p = pop_front_map(p);
		map L = merge_products(p, q);
		L = push_front_map(L, h->begin->tr);
		h = clear_map(h);
		return L;
	}
	q = pop_front_map(q);
	map L = adjoin(h->begin->tr, merge_products(p, q));
	h = clear_map(h);
	return L;
}

static map simplify_product_rec(map L)
{
	Tree* u1 = (L->begin->tr);
	Tree* u2 = (L->end->tr);
	if (L->length == 2 && u1->tok_type != PROD && u2->tok_type != PROD)
	{
		if (isconstant(u1) && isconstant(u2))
		{
			Tree* p = simplify_RNE(join(clone(u1), clone(u2), fnc[PROD].ex));
			L = clear_map(L);
			if (!strcmp(p->value, "1"))
			{
				clean_tree(p);
				return L;
			}
			L = push_back_map(L, p);
			clean_tree(p);
			return L;
		}
		if (!strcmp(u1->value, "1") || !strcmp(u2->value, "1"))
		{
			if (!strcmp(u1->value, "1"))
				L = pop_front_map(L);
			else
				L = pop_back_map(L);
			return L;
		}
		if (tree_compare(base(u1), base(u2)))
		{
			Tree* s = simplify(join(clone(base(u1)), join(exponent(u1), exponent(u2), fnc[ADD].ex), fnc[POW].ex));
			L = clear_map(L);
			map q = push_back_map(L, s);
			if (!strcmp(s->value, "1"))
				q = pop_back_map(q);
			clean_tree(s);
			return q;
		}
		if (u1->tok_type == EXP_F && u2->tok_type == EXP_F)
		{
			Tree* u = simplify(join(join(clone(u1->tleft), clone(u2->tleft), fnc[ADD].ex), NULL, fnc[EXP_F].ex));
			L = clear_map(L);
			L = push_back_map(L, u);
			clean_tree(u);
			return L;
		}
		if (ordre_tree(u2, u1))
		{
			map l = NULL;
			l = push_back_map(l, u2);
			l = push_back_map(l, u1);
			L = clear_map(L);
			return l;
		}
		return L;
	}
	else if (L->length == 2 && (u1->tok_type == PROD || u2->tok_type == PROD))
	{
		map p = map_create_prod(u1);
		map q = map_create_prod(u2);
		L = clear_map(L);
		return merge_products(p, q);
	}
	map k = map_create_prod(u1);
	L = pop_front_map(L);
	map w = simplify_product_rec(L);
	map s = merge_products(k, w);
	return s;
}

static Tree* simplify_product(map L)
{
	int z = 0;
	mapCell* tmp = L->begin;
	while (tmp != NULL)
	{
		if (!strcmp(tmp->tr->value, fnc[UNDEF].ex))
		{
			L = clear_map(L);
			return new_tree(fnc[UNDEF].ex);
		}
		if (!strcmp(tmp->tr->value, "0"))
			z = 1;
		tmp = tmp->next;
	}
	if (z)
	{
		L = clear_map(L);
		return new_tree("0");
	}
	if (L->length == 1)
	{
		Tree* ret = clone(L->begin->tr);
		L = clear_map(L);
		return ret;
	}
	map v = simplify_product_rec(L);
	if (v == NULL)
		return new_tree("1");
	if (v->length == 1)
	{
		Tree* ret = clone(v->begin->tr);
		v = clear_map(v);
		return ret;
	}
	return construct(fnc[PROD].ex, v);
}

static Tree* construct(const char* op, map L)
{
	if (!isop(op))
	{
		Tree* t = join(clone(L->begin->tr), NULL, op);
		L = clear_map(L);
		return t;
	}
	mapCell* tmp = L->begin;
	Tree* tr = NULL;
	while (tmp != NULL)
	{
		tr = (tr == NULL) ? clone(tmp->tr) : join(tr, clone(tmp->tr), op);
		tmp = tmp->next;
	}
	L = clear_map(L);
	return tr;
}

static map merge_sums(map p, map q)
{
	if (!q)
		return p;
	if (!p)
		return q;
	Tree* p1 = p->begin->tr;
	Tree* q1 = q->begin->tr;
	map t = NULL;
	t = push_back_map(t, p1);
	t = push_back_map(t, q1);
	map h = simplify_sum_rec(t);
	if (h == NULL)
	{
		p = pop_front_map(p);
		q = pop_front_map(q);
		return merge_sums(p, q);
	}
	if (h->length == 1)
	{
		p = pop_front_map(p);
		q = pop_front_map(q);
		map L = merge_sums(p, q);
		L = push_front_map(L, h->begin->tr);
		h = clear_map(h);
		return simplify_sum_rec(L);
	}
	if (tree_compare(h->begin->tr, p1))
	{
		p = pop_front_map(p);
		map L = merge_sums(p, q);
		L = push_front_map(L, h->begin->tr);
		h = clear_map(h);
		return L;
	}
	q = pop_front_map(q);
	map L = adjoin(h->begin->tr, merge_sums(p, q));
	h = clear_map(h);
	return L;
}

static map simplify_sum_rec(map L)
{
	if (L->length == 1)
		return L;
	Tree* u1 = (L->begin->tr);
	Tree* u2 = (L->end->tr);
	if (L->length == 2 && (u1->tok_type != ADD && u1->tok_type != SUB) && (u2->tok_type != ADD && u2->tok_type != SUB))
	{
		if (isconstant(u1) && isconstant(u2))
		{
			Tree* p = simplify_RNE(join(clone(u1), clone(u2), fnc[ADD].ex));
			L = clear_map(L);
			if (!strcmp(p->value, "0"))
			{
				clean_tree(p);
				return NULL;
			}
			L = push_back_map(L, p);
			clean_tree(p);
			return L;
		}
		else if (!strcmp(u1->value, "0") || !strcmp(u2->value, "0"))
		{
			if (!strcmp(u1->value, "0"))
				L = pop_front_map(L);
			else
				L = pop_back_map(L);
			return L;
		}
		else if (tree_compare(u1, u2))
		{
			Tree* s = simplify(join(new_tree("2"), clone(u1), fnc[PROD].ex));
			L = clear_map(L);
			map q = push_back_map(L, s);
			clean_tree(s);
			return q;
		}
		Tree* v = denominator_fun(u1), * x = denominator_fun(u2);
		if (!ALG_EXPAND && (strcmp(v->value, "1") || strcmp(x->value, "1")))
		{
			Tree* u = rationalize_sum(u1, u2, fnc[ADD].ex);
			clean_tree(v); clean_tree(x);
			u = simplify(u);
			L = clear_map(L);
			L = push_back_map(L, u);
			clean_tree(u);
			return L;
		}
		clean_tree(v);
		clean_tree(x);
		map map_u1 = map_create_prod(u1), map_u2 = map_create_prod(u2);
		Tree* fact_com = NULL;
		mapCell* tmp0 = map_u1->begin, * tmp1 = NULL;
		bool in_u1;
		while (tmp0 != NULL)
		{
			tmp1 = map_u2->begin;
			in_u1 = false;
			while (tmp1 != NULL)
			{
				if (tree_compare(tmp1->tr, tmp0->tr) && !isconstant(tmp1->tr))
				{
					in_u1 = true;
					fact_com = (fact_com == NULL) ? clone(tmp0->tr) : join(fact_com, clone(tmp0->tr), fnc[PROD].ex);
					clean_tree(tmp1->tr);
					tmp1->tr = new_tree("1");
					break;
				}
				tmp1 = tmp1->next;
			}
			if (in_u1)
			{
				clean_tree(tmp0->tr);
				tmp0->tr = new_tree("1");
			}
			tmp0 = tmp0->next;
		}
		if (fact_com != NULL)
		{
			Tree* term_u1 = construct(fnc[PROD].ex, map_u1);
			Tree* term_u2 = construct(fnc[PROD].ex, map_u2);
			map q = NULL;
			L = clear_map(L);
			v = join(term_u1, term_u2, fnc[ADD].ex);
			v = simplify(v);
			if (!strcmp(v->value, "0") || !strcmp(v->value, "1"))
			{
				if (!strcmp(v->value, "1"))
					q = push_back_map(q, fact_com);
				clean_tree(v);
				clean_tree(fact_com);
				return q;
			}
			v = join(v, fact_com, fnc[PROD].ex);
			q = push_back_map(q, v);
			clean_tree(v);
			return q;
		}
		map_u1 = clear_map(map_u1);
		map_u2 = clear_map(map_u2);
		if (ordre_tree(u2, u1))
		{
			map q = NULL;
			q = push_back_map(q, u2);
			q = push_back_map(q, u1);
			L = clear_map(L);
			return q;
		}
		return L;
	}
	else if (L->length == 2 && (u1->tok_type == ADD || u1->tok_type == SUB || u2->tok_type == ADD || u2->tok_type == SUB))
	{
		map p = map_create_add(u1);
		map q = map_create_add(u2);
		L = clear_map(L);
		return merge_sums(p, q);
	}
	else if (isconstant(u1) && isconstant(L->begin->next->tr))
	{
		Tree* p = simplify_RNE(join(clone(u1), clone(L->begin->next->tr), fnc[ADD].ex));
		L = pop_front_map(L);
		L = pop_front_map(L);
		L = push_front_map(L, p);
		clean_tree(p);
		return simplify_sum_rec(L);
	}
	map p = map_create_add(u1);
	L = pop_front_map(L);
	map w = simplify_sum_rec(L);
	return merge_sums(p, w);
}

static Tree* simplify_sum(map L)
{
	mapCell* tmp = L->begin;
	while (tmp != NULL)
	{
		if (!strcmp(tmp->tr->value, fnc[UNDEF].ex))
		{
			L = clear_map(L);
			return new_tree(fnc[UNDEF].ex);
		}
		tmp = tmp->next;
	}
	if (L->length == 1)
	{
		Tree* ret = clone(L->begin->tr);
		L = clear_map(L);
		return ret;
	}
	map v = simplify_sum_rec(L);
	if (v == NULL)
		return new_tree("0");
	if (v->length == 1)
	{
		Tree* ret = clone(v->begin->tr);
		v = clear_map(v);
		return ret;
	}
	return construct(fnc[ADD].ex, v);
}

static Tree* rationalize_sum(Tree* u, Tree* v, const char* op)
{
	Tree* m = numerator_fun(u), * r = denominator_fun(u);
	Tree* n = numerator_fun(v), * s = denominator_fun(v);
	DList vrs = NULL;
	if (!strcmp(r->value, "1") && !strcmp(s->value, "1"))
	{
		clean_tree(m); clean_tree(r); clean_tree(n); clean_tree(s);
		return join(clone(u), clone(v), op);
	}
	if (tree_compare(r, s))
	{
		Tree* tr = rationalize_sum(m, n, op);
		clean_tree(r); clean_tree(m); clean_tree(n);
		return join(tr, s, fnc[DIVID].ex);
	}
    if (is_int(r) && is_int(s))
    {
        int dr = (int)Eval(r), ds = (int)Eval(s);
        int p = integer_gcd(dr, ds);
        if (p != 1)
        {
            string sp = tostr(p);
            if (dr > ds)
            {
                clean_tree(s);
                n = simplify(join(new_tree(sp), n, fnc[PROD].ex));
                return join(join(m, n, op), r, fnc[DIVID].ex);
            }
            else
            {
                clean_tree(r);
                m = simplify(join(new_tree(sp), m, fnc[PROD].ex));
                return join(join(m, n, op), s, fnc[DIVID].ex);
            }
        }
    }
    /*
    vrs = getvars(r, vrs);
	if (vrs != NULL && ispoly(r, vrs->begin->value) && ispoly(s, vrs->begin->value))
	{
		Tree* dr = degree_sv(r, vrs->begin->value), * ds = degree_sv(s, vrs->begin->value);
		double r1 = Eval(dr), s1 = Eval(ds);
		Tree* gcd = NULL;
		clean_tree(dr); clean_tree(ds);
		if (r1 * s1 > 0)
		{
			if (!(r1 >= s1))
			{
				Tree* tmp = m, * ptmp = r;
				m = n; n = tmp; r = s; s = ptmp;
			}
			gcd = poly_gcd(r, s, vrs->begin->value);
			if (strcmp(gcd->value, "1"))
			{
				Tree* q = poly_quotient(polynomial_division(r, gcd, vrs->begin->value)), * t = NULL;
				m = simplify(join(m, q, fnc[PROD].ex));
				t = rationalize_sum(m, n, op);
				clean_tree(n); clean_tree(m); clean_tree(s); clean_tree(gcd);
				vrs = clear_dlist(vrs);
				return join(t, r, fnc[DIVID].ex);
			}
			vrs = clear_dlist(vrs);
			clean_tree(gcd);
		}
	}
    */
    if (vrs != NULL)
    {
        vrs = clear_dlist(vrs);
    }
	Tree* d = simplify(join(clone(r), clone(s), fnc[PROD].ex));
	Tree* a = simplify(join(m, s, fnc[PROD].ex));
	Tree* b = simplify(join(n, r, fnc[PROD].ex));
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

Tree* contract_exp_rules(Tree* u)
{
	Tree* v = expand_main_op(u);
	if (v->tok_type == POW)
	{
		Tree* b = v->tleft, * s = v->tright;
		if (b->tok_type == EXP_F)
		{
			Tree* p = join(clone(s), clone(b->tleft), fnc[PROD].ex);
			s = contract_exp_rules(p);
			clean_tree(p); clean_tree(v);
			return join(s, NULL, fnc[EXP_F].ex);
		}
	}
	else if (v->tok_type == PROD || v->tok_type == DIVID)
	{
		map L = map_create(v);
		clean_tree(v);
		Tree* s = new_tree("0"), * p = new_tree("1");
		mapCell* tmp = L->begin;
		while (tmp != NULL)
		{
			Tree* q = contract_exp_rules(tmp->tr);
			clean_tree(tmp->tr);
			tmp->tr = q;
			if (tmp->tr->tok_type == EXP_F)
				s = join(s, clone(tmp->tr->tleft), fnc[ADD].ex);
			else
				p = join(p, clone(tmp->tr), fnc[PROD].ex);
			tmp = tmp->next;
		}
		L = clear_map(L);
		s = simplify(s);
		p = simplify(p);
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
	else if (v->tok_type == ADD || v->tok_type == SUB)
	{
		map L = map_create(v);
		clean_tree(v);
		Tree* s = new_tree("0");
		mapCell* tmp = L->begin;
		while (tmp != NULL)
		{
			if (tmp->tr->tok_type == POW || v->tok_type == PROD || v->tok_type == DIVID)
				s = join(s, contract_exp_rules(tmp->tr), fnc[ADD].ex);
			else
				s = join(s, clone(tmp->tr), fnc[PROD].ex);
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
	else
	{
		token tk = u->tok_type;
		if (ADD <= tk && tk <= POW)
			return contract_exp_rules(u);
	}
	return clone(u);
}

Tree* expand_exp_rules(Tree* u)
{
	token tk = u->tok_type;
	if (tk == LN_F)
		return clone(u->tleft);
	if (!strcmp(u->value, "0"))
		return new_tree("1");
	if (tk == ADD || tk == SUB)
		return join(expand_exp_rules(u->tleft), expand_exp_rules(u->tright), fnc[PROD].ex);
	if (tk == PROD)
	{
		if (u->tleft->gtype == ENT)
			return join(expand_exp_rules(u->tright), clone(u->tleft), fnc[POW].ex);
	}
	return join(clone(u), NULL, fnc[EXP_F].ex);
}

static Tree* expand_exp(Tree* u)
{
	if (u->tok_type == EXP_F)
		return expand_exp_rules(u->tleft);
	return clone(u);
}

static Tree* simplify_exp(Tree* u)
{
	Tree* p = expand_exp(u);
	Tree* s = contract_exp(p);
	clean_tree(p);
	return s;
}

static Tree* contract_ln_rules(Tree* u)
{
	Tree* v = clone(u);
	if (v->tok_type == ADD || v->tok_type == SUB)
	{
		map L = map_create_add(v);
		clean_tree(v);
		Tree* p = NULL, * s = NULL;
		mapCell* item = L->begin;
		while (item != NULL)
		{
			Tree* q = contract_ln_rules(item->tr);
			clean_tree(item->tr);
			item->tr = q;
			if (item->tr->tok_type == LN_F)
				s = (s == NULL) ? clone(item->tr->tleft) : join(s, clone(item->tr->tleft), fnc[PROD].ex);
			else
				p = (p == NULL) ? clone(item->tr) : join(p, clone(item->tr), fnc[ADD].ex);
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
		clean_tree(v);
		Tree* s = NULL;
		mapCell* item = L->begin;
		while (item != NULL)
		{
			if (item->tr->tok_type == ADD || item->tr->tok_type == SUB)
				s = (s == NULL) ? contract_ln_rules(item->tr) : join(s, contract_ln_rules(item->tr), fnc[ADD].ex);
			else
				s = (s == NULL) ? clone(item->tr) : join(s, clone(item->tr), fnc[PROD].ex);
			item = item->next;
		}
		L = clear_map(L);
		return s;
	}
	return v;
}

static Tree* contract_ln(Tree* u)
{
	if (u->gtype <= VAR || isconstant(u))
		return clone(u);
	else
	{
		token tk = u->tok_type;
		if (ADD == tk && tk < POW)
			return contract_ln_rules(u);
	}
	return clone(u);
}

Tree* expand_ln_rules(Tree* u)
{
	if (u->tok_type == EXP_F)
		return clone(u->tleft);
	if (!strcmp(u->value, "0"))
		return new_tree(fnc[UNDEF].ex);
	if (!strcmp(u->value, "1"))
		return new_tree("0");
	if (u->gtype == ENT)
	{
		Tree* tr = factorn(tonumber(u->value));
		if (tr->tok_type == PROD || tr->tok_type == POW)
		{
			Tree* t = expand_ln_rules(tr);
			clean_tree(tr);
			return t;
		}
		else
		{
			clean_tree(tr);
			return join(clone(u), NULL, fnc[LN_F].ex);
		}
	}
	if (u->tok_type == PROD)
		return join(expand_ln_rules(u->tleft), expand_ln_rules(u->tright), fnc[ADD].ex);
	if (u->tok_type == DIVID)
		return join(expand_ln_rules(u->tleft), expand_ln_rules(u->tright), fnc[SUB].ex);
	if (u->tok_type == POW && is_symbolic(u->tleft))
		return join(clone(u->tright), expand_ln_rules(u->tleft), fnc[PROD].ex);
	return join(clone(u), NULL, fnc[LN_F].ex);
}

static Tree* expand_ln(Tree* u)
{
	if (u->tok_type == LN_F)
		return expand_ln_rules(u->tleft);
	return clone(u);
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
		return u;
	if (u->tok_type == DIVID)
		return join(absolute_value(u->tleft), absolute_value(u->tright), u->value);
	if (u->tok_type == POW && u->tright->gtype == ENT)
		return join(absolute_value(u->tleft), u->tright, fnc[POW].ex);
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
			Tree* tmp = absolute_value(item->tr);
			if (tmp->tok_type == ABS_F)
				s = join(s, tmp->tleft, fnc[PROD].ex);
			else
				r = join(r, tmp, fnc[PROD].ex);
			item = item->next;
		}
		s = simplify(s);
		r = simplify(r);
		if (!strcmp(s->value, "1"))
		{
			clean_tree(s);
			return r;
		}
		if (!strcmp(r->value, "1"))
		{
			clean_tree(r);
			return join(s, NULL, fnc[ABS_F].ex);
		}
		return join(r, join(s, NULL, fnc[ABS_F].ex), fnc[PROD].ex);
	}
	if ((u->tok_type == ADD || u->tok_type == SUB) && found_element(u, fnc[IMAGE].ex))
	{
		Tree* z = new_tree("0"), * o = new_tree("1");
		Tree* a = coefficient_gpe(u->tright, fnc[IMAGE].ex, z), * b = coefficient_gpe(u->tright, fnc[IMAGE].ex, o);
		clean_tree(z); clean_tree(o);
		o = join(join(a, new_tree("2"), fnc[POW].ex), join(b, new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
		return simplify(o);
	}
	return join(u, NULL, fnc[ABS_F].ex);
}

Tree* Contract_pow(Tree* v)
{
	if (v->tok_type == POW)
	{
		Tree* tr = join(Contract_pow(v->tleft), v->tright, v->value);
		clean_noeud(v);
		return tr;
	}
	if (v->tok_type == ADD || v->tok_type == SUB)
	{
		Tree* tr = join(Contract_pow(v->tleft), Contract_pow(v->tright), v->value);
		clean_noeud(v);
		return tr;
	}
	else if (v->tok_type == PROD || v->tok_type == DIVID)
	{
		map L = map_create(v), q = NULL, s = NULL;
		clean_tree(v);
		Tree* p = NULL;
		mapCell* item = L->begin;
		while (item != NULL)
		{
			if (item->tr->tok_type == POW)
			{
				int index = -1;
				if (q != NULL)
				{
					mapCell* tmp = q->begin;
					mapCell* tmp1 = s->begin;
					index = 1;
					while (tmp != NULL)
					{
						if (tree_compare(tmp->tr, item->tr->tright))
						{
							tmp1->tr = join(tmp1->tr, clone(item->tr->tleft), fnc[PROD].ex);
							if (RT_SIMP)
								tmp1->tr = simplify(tmp1->tr);
							break;
						}
						index++;
						tmp = tmp->next;
						tmp1 = tmp1->next;
					}
				}
				if (index == -1 || index > q->length)
				{
					q = push_back_map(q, item->tr->tright);
					s = push_back_map(s, item->tr->tleft);
				}
			}
			else
				p = (p == NULL) ? clone(item->tr) : join(p, clone(item->tr), fnc[PROD].ex);
			item = item->next;
		}
		L = clear_map(L);
		if (q != NULL)
		{
			mapCell* tmp = q->begin;
			mapCell* tmp1 = s->begin;
			while (tmp != NULL)
			{
				p = (p == NULL) ? join(clone(tmp1->tr), clone(tmp->tr), fnc[POW].ex) : join(p, join(clone(tmp1->tr), clone(tmp->tr), fnc[POW].ex), fnc[PROD].ex);
				tmp = tmp->next;
				tmp1 = tmp1->next;
			}
			q = clear_map(q);
			s = clear_map(s);
		}
		return p;
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
	if (!strcmp(u->value, x) || !found_element(u, x))
		return true;
	if (u->tok_type == POW)
		return ismonomial(u->tleft, x) && u->tright->gtype == ENT;
	if (u->tok_type == PROD)
		return ismonomial(u->tleft, x) && ismonomial(u->tright, x);
	if (u->tok_type == DIVID)
		return ismonomial(u->tleft, x) && !ismonomial(u->tright, x);
	if (u->tok_type == NEGATIF)
		return ismonomial(u->tleft, x);
	return false;
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
			Tree* f = degree_monomial_sv(tmp->tr, x);
			if (!strcmp(f->value, fnc[UNDEF].ex))
			{
				clean_tree(d);
				L = clear_map(L);
				return f;
			}
			else
			{
				double e = Eval(d), g = Eval(f);
				if (e < g)
				{
					clean_tree(d);
					d = clone(f);
				}
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

Tree* degree_monomial_sv(Tree* u, const char* x)
{
	if (!strcmp(u->value, "0"))
		return join(new_tree("1"), NULL, fnc[NEGATIF].ex);
	else if (isconstant(u))
		return new_tree("0");
	else if (!strcmp(u->value, x))
		return new_tree("1");
	else if (u->tok_type == POW)
	{
		Tree* b = u->tleft;
		Tree* e = u->tright;
		if (!strcmp(b->value, x) && e->gtype == ENT)
		{
			double f = Eval(e);
			if (f >= 1)
				return clone(e);
		}
	}
	else if (u->tok_type == NEGATIF || u->tok_type == DIVID)
		return degree_monomial_sv(u->tleft, x);
	else if (u->tok_type == PROD)
	{
		Tree* s = degree_monomial_sv(u->tleft, x);
		Tree* t = degree_monomial_sv(u->tright, x);
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

map coefficient_monomial_gpe(Tree* u, const char* x)
{
	map L = NULL;
	if (!strcmp(u->value, x))
	{
		Tree* un = new_tree("1");
		L = push_back_map(L, un);
		L = push_back_map(L, un);
		clean_tree(un);
		return L;
	}
	else if (u->tok_type == NEGATIF)
	{
		L = coefficient_monomial_gpe(u->tleft, x);
		L->begin->tr = simplify(join(L->begin->tr, NULL, fnc[NEGATIF].ex));
		return L;
	}
	else if (u->tok_type == DIVID)
	{
		L = coefficient_monomial_gpe(u->tleft, x);
		L->begin->tr = simplify(join(L->begin->tr, clone(u->tright), fnc[DIVID].ex));
		return L;
	}
	else if (u->tok_type == POW)
	{
		Tree* b = u->tleft;
		Tree* e = u->tright;
		if (!strcmp(b->value, x) && e->gtype == ENT)
		{
			double f = Eval(e);
			if (f > 1)
			{
				Tree* un = new_tree("1");
				L = push_back_map(L, un);
				L = push_back_map(L, e);
				clean_tree(un);
				return L;
			}
		}
	}
	else if (u->tok_type == PROD)
	{
		Tree* m = new_tree("0"), * c = clone(u);
		map M = map_create_prod(u);
		mapCell* tmp = M->begin;
		while (tmp != NULL)
		{
			map f = coefficient_monomial_gpe(tmp->tr, x);
			if (f == NULL)
			{
				clean_tree(m);
				clean_tree(c);
				M = clear_map(M);
				return f;
			}
			else if (strcmp(f->end->tr->value, "0"))
			{
				clean_tree(m);
				m = clone(f->end->tr);
				clean_tree(c);
				c = simplify(join(clone(u), join(new_tree(x), clone(m), fnc[POW].ex), fnc[DIVID].ex));
			}
			f = clear_map(f);
			tmp = tmp->next;
		}
		L = push_back_map(L, c);
		L = push_back_map(L, m);
		clean_tree(m);
		clean_tree(c);
		M = clear_map(M);
		return L;
	}
	Tree* tx = new_tree(x);
	if (free_of(u, tx))
	{
		Tree* zero = new_tree("0");
		L = push_back_map(L, u);
		L = push_back_map(L, zero);
		clean_tree(zero);
	}
	clean_tree(tx);
	return L;
}

Tree* coefficient_gpe(Tree* u, const char* x, Tree* j)
{
	if (u->tok_type != ADD && u->tok_type != SUB)
	{
        if (!strcmp(u->value, x))
		{
			if (!strcmp(j->value, "1"))
				return new_tree("1");
			return new_tree("0");
		}
		if (u->tok_type == NEGATIF)
		{
			Tree* cf = coefficient_gpe(u->tleft, x, j);
			if (strcmp(cf->value, fnc[UNDEF].ex))
				return simplify(join(cf, NULL, fnc[NEGATIF].ex));
			return cf;
		}
		else if (u->tok_type == DIVID)
		{
			Tree* cf = coefficient_gpe(u->tleft, x, j);
			if (strcmp(cf->value, fnc[UNDEF].ex))
				return simplify(join(cf, clone(u->tright), fnc[DIVID].ex));
			return cf;
		}
		else if (u->tok_type == PROD && (u->tright->tok_type == ADD || u->tright->tok_type == SUB))
		{
			Tree* cf = coefficient_gpe(u->tright, x, j);
			if (strcmp(cf->value, fnc[UNDEF].ex))
				return simplify(join(cf, clone(u->tleft), fnc[PROD].ex));
			return cf;
		}
		map f = coefficient_monomial_gpe(u, x);
		if (f == NULL)
		{
			f = clear_map(f);
			return new_tree(fnc[UNDEF].ex);
		}
		if (tree_compare(j, f->end->tr))
		{
			Tree* c = clone(f->begin->tr);
			f = clear_map(f);
			return c;
		}
		f = clear_map(f);
		return new_tree("0");
	}
	else
	{
		Tree* c = NULL;
		map L = map_create_add(u);
		mapCell* tmp = L->begin;
        while (tmp != NULL)
		{
			map f = coefficient_monomial_gpe(tmp->tr, x);
			if (f == NULL)
			{
				if (c != NULL)
					clean_tree(c);
				f = clear_map(f);
				L = clear_map(L);
				return new_tree(fnc[UNDEF].ex);
			}
			else if (tree_compare(f->end->tr, j))
			{
				if (c == NULL)
					c = clone(f->begin->tr);
				else
					c = join(c, clone(f->begin->tr), fnc[ADD].ex);
			}
			f = clear_map(f);
			tmp = tmp->next;
		}
		L = clear_map(L);
		if (c == NULL)
			return new_tree("0");
		return c;
	}
}

map polynomial_division(Tree* u, Tree* v, const char* x) // page 116
{
	Tree* q = new_tree("0");
	Tree* r = clone(u);
	Tree* dr = degree_sv(r, x);
	Tree* dv = degree_sv(v, x);
	map L = NULL;
	int m = (int)Eval(dr), n = (int)Eval(dv);
	Tree* lcv = coefficient_gpe(v, x, dv);
	while (m >= n)
	{
		Tree* lcr = coefficient_gpe(r, x, dr);
		Tree* s = join(lcr, clone(lcv), fnc[DIVID].ex);
        Tree* p = join(s, join(new_tree(x), join(dr, clone(dv), fnc[SUB].ex), fnc[POW].ex), fnc[PROD].ex);
		q = join(q, clone(p), fnc[ADD].ex);
        r = simplify(join(r, join(clone(v), p, fnc[PROD].ex), fnc[SUB].ex));
		dr = degree_sv(r, x);
		m = (int)Eval(dr);
	}
	clean_tree(dr);
	clean_tree(dv);
	L = push_back_map(L, q);
	L = push_back_map(L, r);
	clean_tree(q);
	clean_tree(r);
	clean_tree(lcv);
	return L;
}

Tree* poly_quotient(map L)
{
	Tree* tr = clone(L->begin->tr);
	L = clear_map(L);
	return simplify(tr);
}

Tree* poly_remainder(map L)
{
	Tree* tr = clone(L->end->tr);
	L = clear_map(L);
	return tr;
}

Tree* poly_gcd(Tree* u, Tree* v, const char* x)
{
	if (!strcmp(u->value, "0") && !strcmp(v->value, "0"))
		return new_tree("1");
	Tree* U = clone(u), * V = clone(v);
	while (strcmp(V->value, "0"))
	{
		Tree* R = poly_remainder(polynomial_division(U, V, x));
		clean_tree(U);
		U = clone(V);
		clean_tree(V);
		V = R;
	}
	clean_tree(V);
	Tree* dr = degree_sv(U, x);
	Tree* lcr = coefficient_gpe(U, x, dr);
	clean_tree(dr);
	return simplify(join(join(new_tree("1"), lcr, fnc[DIVID].ex), U, fnc[PROD].ex));
}

Tree* poly_simp(Tree* u, Tree* v, const char* x)
{
	Tree* deg_u = degree_sv(u, x);
	Tree* deg_v = degree_sv(v, x);
	double a = Eval(deg_u), b = Eval(deg_v);
	clean_tree(deg_u);
	clean_tree(deg_v);
	if (a > 0 && b > 0 && ((u->tok_type == SUB || u->tok_type == ADD) && (v->tok_type == SUB || v->tok_type == ADD)))
	{
		Tree* pgcd = poly_gcd(u, v, x);
		if (strcmp(pgcd->value, "1"))
		{
			Tree* ql = poly_quotient(polynomial_division(u, pgcd, x));
			Tree* qr = poly_quotient(polynomial_division(v, pgcd, x));
			clean_tree(pgcd);
			if (!strcmp(qr->value, "1"))
			{
				clean_tree(qr);
				return ql;
			}
			return join(ql, join(qr, join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex), fnc[PROD].ex);
		}
		clean_tree(pgcd);
	}
	return join(u, join(v, join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex), fnc[PROD].ex);
}

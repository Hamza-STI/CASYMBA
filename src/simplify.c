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
	{ "1/6*PI", "sqrt(3)/2", "1/2", "sqrt(3)/3" },
	{ "1/4*PI", "sqrt(2)/2", "sqrt(2)/2", "1" },
	{ "1/3*PI", "1/2", "sqrt(3)/2", "sqrt(3)" },
	{ "1/2*PI", "1", "0", fnc[UNDEF].ex },
	{ "2/3*PI", "~1/2", "sqrt(3)/2", "~sqrt(3)" },
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

int ispoly(Tree* u, const char* vr)
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

int is_int(Tree* u)
{
	if (u->tok_type == NEGATIF)
		return is_int(u->tleft);
	return (u->gtype == ENT);
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
	else if (u->gtype == OPERAT)
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
				a = (ordre_tree(a, c)) ? join(a, c, fnc[PROD].ex) : join(c, a, fnc[PROD].ex);
				b = (ordre_tree(b, d)) ? join(b, d, fnc[PROD].ex) : join(d, b, fnc[PROD].ex);
				u = join(a, b, fnc[DIVID].ex);
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

Tree* base(Tree* u)
{
	return (u->tok_type == POW) ? u->tleft : u;
}

Tree* exponent(Tree* u)
{
	return (u->tok_type == POW) ? clone(u->tright) : new_tree("1");
}

long long int factoriel(long long int a)
{
	long long int s = 1, i;
	for (i = 1; i <= a; i++)
		s *= i;
	return s;
}

double fpart(double ex)
{
	return (double)(ex - ((long long int)ex));
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
		Tree* f = u->tleft, * r = u->tright, * s = NULL;
		for (int i = 0; i <= n; i++)
		{
			Tree* g = join(clone(f), new_tree(tostr(n - i)), fnc[POW].ex);
			double c = (double)factoriel(n) / (factoriel(i) * factoriel(n - i));
			Tree* a = simplify(join(new_tree(tostr(c)), g, fnc[PROD].ex)), * b = simplify(expand_power(r, i));
			Tree* t = expand_product(a, b);
			s = (s == NULL) ? t : join(s, t, u->value);
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

Tree* expand_main_op(Tree* u)
{
	if (u->tok_type == DIVID)
	{
		Tree* r = u->tleft;
		if (r->tok_type == ADD || r->tok_type == SUB)
		{
			map L = map_create_add(r);
			mapCell* tmp = L->begin;
			Tree* tr = NULL;
			while (tmp != NULL)
			{
				Tree* w = join(clone(tmp->tr), clone(u->tright), fnc[DIVID].ex);
				tr = (!tr) ? w : join(tr, w, fnc[ADD].ex);
				tmp = tmp->next;
			}
			L = clear_map(L);
			return tr;
		}
	}
	if (u->tok_type == PROD)
	{
		Tree* r = u->tleft, * s = u->tright;
		if (r->tok_type == ADD || r->tok_type == SUB)
		{
			map L = map_create_add(r), M = map_create_add(s);
			mapCell* tmp = L->begin;
			Tree* tr = NULL;
			while (tmp != NULL)
			{
				mapCell* tmp1 = M->begin;
				while (tmp1 != NULL)
				{
					Tree* w = join(clone(tmp->tr), clone(tmp1->tr), fnc[PROD].ex);
					tr = (!tr) ? w : join(tr, w, fnc[ADD].ex);
					tmp1 = tmp1->next;
				}
				tmp = tmp->next;
			}
			L = clear_map(L);
			M = clear_map(M);
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
	if (u->tok_type == POW && u->tright->gtype == ENT && ALG_EXPAND)
	{
		int d = (int)Eval(u->tright);
		if (d <= 10)
			return expand_power(u->tleft, d);
	}
	return clone(u);
}

int ordre_tree1(Tree* u, Tree* v)
{
	map p = map_create(u), q = map_create(v);
	if (!tree_compare(p->end->tr, q->end->tr))
	{
		int k = ordre_tree(p->end->tr, q->end->tr);
		p = clear_map(p);
		q = clear_map(q);
		return k;
	}
	mapCell* tmp = p->end, * tmp1 = q->end;
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
	int k = p->length < q->length;
	p = clear_map(p);
	q = clear_map(q);
	return k;
}

int cmpvar(Tree* u, Tree* v)
{
	string p = u->value, q = v->value;
	int a = strlen(p), b = strlen(q), k = 0;
	int i = (a >= b) ? a : b;
	while (k < i && p[k] == q[k])
		k++;
	return k < i && p[k] < q[k];
}

int ordre_tree(Tree* u, Tree* v)
{
	if (isconstant(u) && isconstant(v))
		return Eval(u) < Eval(v);
	if (u->gtype == VAR && v->gtype == VAR)
		return cmpvar(u, v);
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
		return (u->tok_type != v->tok_type) ? cmpvar(u, v) : ordre_tree1(u->tleft, v->tleft);
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
	{
		Tree* tr = join(clone(v), new_tree("1"), fnc[POW].ex);
		int k = !ordre_tree(tr, u);
		clean_tree(tr);
		return k;
	}
	if (u->tok_type != POW && v->tok_type == POW)
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
				Tree* t = tmp1->tr;
				tmp1->tr = tmp->tr;
				tmp->tr = t;
			}
			tmp1 = tmp1->next;
		}
		tmp = tmp->next;
	}
	return li;
}

Tree* trigo_identify(const char* s, token tk)
{
	for (const Trigo_value* element = Exact_Values; element != Exact_Values + AMONT_VALUE_TRIG; element++)
	{
		if ((tk == COS_F || tk == SIN_F || tk == TAN_F) && !strcmp(s, element->angle))
		{
			if (tk == COS_F)
				return to_tree(In2post2(element->cos_value));
			return to_tree(In2post2((tk == SIN_F) ? element->sin_value : element->tan_value));
		}
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

char* zero_untile(const char* a)
{
	if (!strcmp(a, "0"))
		return strdup("0");
	int len_a = strlen(a), i = 0;
	int k = len_a - 1, pos = 0;
	char* c = strchr(a, '.');
	while (a[i] == '0' || (a[k] == '0' && c != NULL))
	{
		if (a[i] == '0')
			i++;
		if (a[k] == '0' && c != NULL)
			k--;
	}
	if (a[i] == '.' || i == len_a)
		i--;
	if (a[k] == '.')
		k--;
	char* b = malloc((k - i + 2) * sizeof(char));
	for (int j = 0; j < len_a; j++)
	{
		if (i <= j && j <= k)
		{
			b[pos] = a[j];
			pos++;
		}
		if (j >= k)
			break;
	}
	if (pos == 0)
	{
		b[pos] = '0';
		pos++;
	}
	b[pos] = '\0';
	return b;
}

bool greater(const char* a, const char* b)
{
	char* c = strchr(a, '.'), * d = strchr(b, '.');
	int len_c = (c == NULL) ? 0 : strlen(c), len_d = (d == NULL) ? 0 : strlen(d);
	int len_a = strlen(a) - len_c, len_b = strlen(b) - len_d;
	int n = (len_c < len_d) ? len_c : len_d;
	if (len_a != len_b)
		return len_a > len_b;
	for (int i = 0; i < len_a + n; i++)
	{
		if (a[i] != b[i])
			return a[i] > b[i];
	}
	return false;
}

char* new_value(const char* a, unsigned size_int_a, unsigned size_dec_a, unsigned new_size_int, unsigned new_size_dec)
{
	if (strlen(a) == new_size_int + new_size_dec)
		return strdup(a);
	char* ret = malloc(new_size_int + new_size_dec + 1);
	int length = new_size_int - size_int_a;
	for (int i = 0; i < length; i++)
		ret[i] = '0';
	for (unsigned i = 0; i < strlen(a); i++)
	{
		ret[length] = a[i];
		length++;
	}
	if (new_size_dec && !size_dec_a)
	{
		ret[length] = '.';
		length++;
	}
	for (unsigned i = 1; i <= new_size_dec - size_dec_a; i++)
	{
		ret[length] = '0';
		length++;
	}
	return ret;
}

int sub_cc(char a, char b, int* retenue)
{
	int r = a - '0', s = (b - '0') + (*retenue);
	if (r < s)
	{
		r += 10;
		*retenue = 1;
	}
	else
		*retenue = 0;
	return r - s;
}

int add_cc(char a, char b, int* retenue)
{
	int w = ((a - '0') + (b - '0')) + (*retenue);
	if (w >= 10)
	{
		w -= 10;
		*retenue = 1;
	}
	else
		*retenue = 0;
	return w;
}

char* adds(const char* left, const char* right, int op)
{
	char* c = strchr(left, '.'), * d = strchr(right, '.');
	int len_c = (c == NULL) ? 0 : strlen(c), len_d = (d == NULL) ? 0 : strlen(d);
	int len_a = strlen(left) - len_c, len_b = strlen(right) - len_d;
	int m = (len_a > len_b) ? len_a : len_b, n = (len_c > len_d) ? len_c : len_d, pos = 0, retenue = 0;
	char clc[50] = { 0 };
	char* new_a = new_value(left, len_a, len_c, m, n), * new_b = new_value(right, len_b, len_d, m, n);
	for (int i = m + n - 1; i >= 0; --i)
	{
		if (new_a[i] == '.')
			clc[pos] = '.';
		else
			clc[pos] = '0' + ((op == 1) ? add_cc(new_a[i], new_b[i], &retenue) : sub_cc(new_a[i], new_b[i], &retenue));
		pos++;
	}
	if (op == 1 && retenue == 1)
		clc[pos] = '1';
	else
		pos--;
	while (clc[pos] == '0')
		pos--;
	char* ret = malloc((pos + 2) * sizeof(char));
	for (int i = pos; i >= 0; --i)
		ret[pos - i] = clc[i];
	ret[pos + 1] = '\0';
	free(new_a); free(new_b);
	char* z = zero_untile(ret);
	free(ret);
	return z;
}

char* sub(const char* left, const char* right, int* sign)
{
	if (!strcmp(left, right))
		return strdup("0");
	if (greater(right, left))
	{
		if (sign != NULL)
			*sign = -1;
		return sub(right, left, sign);
	}
	return adds(left, right, -1);
}

char* add(const char* left, const char* right)
{
	return adds(left, right, 1);
}

char* prod(const char* left, const char* right)
{
	char* c = strchr(left, '.'), * d = strchr(right, '.');
	int len_a = strlen(left), len_b = strlen(right), len_c = (c == NULL) ? 0 : strlen(c) - 1, len_d = (d == NULL) ? 0 : strlen(d) - 1;
	int pos = 0, retenue = 0, w = 0, s = 0;
	char clc[50] = { 0 }, n_clc[50] = { 0 }, tmp[50] = { 0 };
	for (int i = len_a - 1; i >= 0; i--)
	{
		if (left[i] != '.')
		{
			pos = 0;
			retenue = 0;
			for (int k = 0; k < s; k++)
			{
				clc[pos] = '0';
				pos++;
			}
			s++;
			for (int k = len_b - 1; k >= 0; k--)
			{
				if (right[k] != '.')
				{
					w = ((left[i] - '0') * (right[k] - '0')) + retenue;
					retenue = w / 10;
					if (retenue > 0)
						w -= retenue * 10;
					clc[pos] = '0' + w;
					pos++;
				}
			}
			if (retenue > 0)
				clc[pos] = '0' + retenue;
			else
				pos--;
			for (int k = pos; k >= 0; k--)
			{
				n_clc[pos - k] = clc[k];
				clc[k] = '\0';
			}
			if (strlen(tmp) == 0)
				strcpy(tmp, n_clc);
			else
			{
				char r[50] = { 0 };
				strcpy(r, n_clc);
				char* t = add(r, tmp);
				strcpy(tmp, t);
				free(t);
			}
		}
	}
	pos = 0;
	s = strlen(tmp);
	char* ret = malloc((s + 2) * sizeof(char));
	for (int i = 0; i < s; i++)
	{
		ret[pos] = tmp[i];
		pos++;
		if (s - (i + 1) == len_c + len_d)
		{
			ret[pos] = '.';
			pos++;
		}
	}
	if (ret[s - 1] == '.')
		ret[s - 1] = '\0';
	ret[s] = '\0';
	char* z = zero_untile(ret);
	free(ret);
	return z;
}

char* int_divid(const char* num, const char* denom, char** rem)
{
	int len_a = strlen(num), len_b = strlen(denom), pos = 0, p = 0;
	char tmp[50] = { 0 }, quot[50] = { 0 };
	for (int i = 0; i < len_b; i++)
	{
		if (i == len_a)
		{
			pos++;
			break;
		}
		tmp[pos] = num[i];
		pos++;
	}
	do {
		int k = 1;
		while (k < 10)
		{
			char w[2] = { '0' + k, '\0' };
			char* n = prod(denom, w);
			bool sup = greater(n, tmp);
			if (!strcmp(n, tmp))
			{
				k++;
				free(n);
				break;
			}
			free(n);
			if (sup)
				break;
			k++;
		}
		k--;
		char u[2] = { '0' + k, '\0' };
		char* m = prod(denom, u);
		char* v = sub(tmp, m, NULL);
		memset(tmp, 0, 50 * sizeof(char));
		if (strcmp(v, "0"))
			strcpy(tmp, v);
		free(v); free(m);
		if ((k == 0 && p > 0) || k > 0)
		{
			quot[p] = '0' + k;
			p++;
		}
		if (pos < len_a)
			tmp[strlen(tmp)] = num[pos];
		pos++;
	} while (pos <= len_a);
	char* t = zero_untile(quot);
	char* ret = strdup(t);
	free(t);
	if (strlen(tmp) == 0)
		tmp[0] = '0';
	if (rem != NULL)
	{
		char* r = zero_untile(tmp);
		*rem = strdup(r);
		free(r);
	}
	return ret;
}

char* divid(const char* num, const char* denom)
{
	char* c = strchr(num, '.'), * d = strchr(denom, '.');
	int len_c = (c == NULL) ? 0 : strlen(c) - 1, len_d = (d == NULL) ? 0 : strlen(d) - 1;
	int len_a = strlen(num), len_b = strlen(denom), pos = 0, prec = 0, p = 0;
	char new_a[50] = { 0 }, new_b[50] = { 0 }, tmp[50] = { 0 }, quot[50] = { 0 };
	bool digit = false;
	if (len_d > 0)
	{
		if (!len_c)
		{
			strcpy(new_a, num);
			for (int i = 0; i < len_d; i++)
				new_a[len_a + i] = '0';
		}
		else
		{
			pos = 0;
			for (int i = 0; i < len_a; i++)
			{
				if (num[i] == '.')
					digit = true;
				else if (digit)
				{
					if (len_d == 0)
					{
						new_a[pos] = '.';
						pos++;
					}
					new_a[pos] = num[i];
					pos++;
					len_d--;
				}
				else
				{
					new_a[pos] = num[i];
					pos++;
				}
			}
			while (len_d > 0)
			{
				new_a[pos] = '0';
				pos++;
				len_d--;
			}
		}
		pos = 0;
		for (int i = 0; i < len_b; i++)
		{
			if (denom[i] != '.')
			{
				new_b[pos] = denom[i];
				pos++;
			}
		}
	}
	else
	{
		strcpy(new_a, num);
		strcpy(new_b, denom);
	}
	pos = 0;
	len_b = strlen(new_b);
	len_a = strlen(new_a);
	digit = false;
	for (int i = 0; i < len_b; i++)
	{
		if (new_a[i] == '.')
			digit = true;
		if (digit || i == len_a)
		{
			tmp[pos] = new_a[i + 1];
			pos += 2;
			quot[0] = '0';
			quot[1] = '.';
			p = 2;
			break;
		}
		tmp[pos] = new_a[i];
		pos++;
	}
	while (prec < 15)
	{
		int k = 1;
		while (k < 10)
		{
			char w[2] = { '0' + k, '\0' };
			char* n = prod(new_b, w);
			bool sup = greater(n, tmp);
			free(n);
			if (sup)
				break;
			k++;
		}
		k--;
		char u[2] = { '0' + k, '\0' };
		char* m = prod(new_b, u);
		char* v = sub(tmp, m, NULL);
		memset(tmp, 0, 50 * sizeof(char));
		if (strcmp(tmp, "0"))
			strcpy(tmp, v);
		free(v); free(m);
		quot[p] = '0' + k;
		p++;
		if (!strcmp(tmp, "0") && pos >= len_a)
			break;
		if ((pos < len_a && new_a[pos] == '.') || pos == len_a)
		{
			digit = true;
			pos++;
			quot[p] = '.';
			p++;
		}
		else if (digit)
			prec++;
		tmp[strlen(tmp)] = (pos >= len_a) ? '0' : new_a[pos];
		pos++;
	}
	return strdup(quot);
}

char* gcd(const char* num, const char* denom)
{
	if (!strcmp(num, "1") || !strcmp(denom, "1"))
		return strdup("1");
	if (!strcmp(num, denom))
		return strdup(num);
	if (greater(denom, num))
		return gcd(denom, num);
	char* rem, * d = strdup(denom);
	char* q = int_divid(num, denom, &rem);
	free(q);
	while (strcmp(rem, "0"))
	{
		char* tmp;
		char* q1 = int_divid(d, rem, &tmp);
		free(d); d = strdup(rem);
		free(q1); free(rem);
		rem = tmp;
	}
	free(rem);
	return d;
}

static Tree* fracOp(const char* numerator, const char* denominator)
{
	if (!strcmp(numerator, "0"))
		return new_tree(numerator);
	string in = strchr(numerator, '.'), id = strchr(denominator, '.');
	if (in == NULL && id == NULL)
	{
		char* pgcd = gcd(numerator, denominator);
		char* a_str = int_divid(numerator, pgcd, NULL), * b_str = int_divid(denominator, pgcd, NULL);
		Tree* tr = (!strcmp(b_str, "1")) ? new_tree(a_str) : join(new_tree(a_str), new_tree(b_str), fnc[DIVID].ex);
		free(pgcd); free(a_str); free(b_str);
		return tr;
	}
	char* w = divid(numerator, denominator);
	Tree* tr = new_tree(w);
	free(w);
	return tr;
}

static Tree* sumOp(const char* left, const char* right)
{
	char* ret = add(left, right);
	Tree* tr = new_tree(ret);
	free(ret);
	return tr;
}

static Tree* diffOp(const char* left, const char* right)
{
	int sign = 1;
	char* ret = sub(left, right, &sign);
	Tree* tr = new_tree(ret);
	free(ret);
	if (sign != 1)
		return join(tr, NULL, fnc[NEGATIF].ex);
	return tr;
}

static Tree* prodOp(const char* left, const char* right)
{
	char* ret = prod(left, right);
	Tree* tr = new_tree(ret);
	free(ret);
	return tr;
}

static Tree* factOp(const char* left)
{
	string in = strchr(left, '.');
	if (!in)
		return new_tree(tostr(factoriel(strtoull(left, NULL, 10))));
	return new_tree(fnc[UNDEF].ex);
}

static Tree* simplify_rational_number(Tree* u)
{
	if (count_tree_nodes(u) == 3 && u->tok_type == DIVID)
		return fracOp(u->tleft->value, u->tright->value);
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
	clean_tree(t);
	Tree* i = simplify_RNE_rec(join(numerator_fun(left), denominator_fun(right), fnc[PROD].ex));
	Tree* j = simplify_RNE_rec(join(numerator_fun(right), denominator_fun(left), fnc[PROD].ex));
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
			Tree* r = new_tree("1"), * s = evaluate_power(bases, expon->tleft);
			Tree* t = evaluate_quotient(r, s);
			clean_tree(r); clean_tree(s);
			return t;
		}
		Tree* u = numerator_fun(bases);
		if (e > 0)
		{
			Tree* r = join(u, clone(expon), fnc[POW].ex), * s = join(v, clone(expon), fnc[POW].ex);
			double f = Eval(s);
			e = Eval(r);
			clean_tree(s);
			clean_tree(r);
			return join(new_tree(tostr(e)), new_tree(tostr(f)), fnc[DIVID].ex);
		}
		Tree* r = evaluate_power(v, expon->tleft), * s = evaluate_power(u, expon->tleft);
		clean_tree(u); clean_tree(v);
		u = evaluate_quotient(r, s);
		clean_tree(r); clean_tree(s);
		return u;
	}
	clean_tree(tr);
	return (e < 0) ? new_tree(fnc[UNDEF].ex) : new_tree("0");
}

static Tree* evaluate_add(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0"))
		return clone(right);
	if (!strcmp(right->value, "0"))
		return clone(left);
	if (count_tree_nodes(left) == 1 && count_tree_nodes(right) == 1)
		return sumOp(left->value, right->value);
	else if (left->tok_type == NEGATIF)
		return evaluate_diff(right, left->tleft);
	else if (right->tok_type == NEGATIF)
		return evaluate_diff(left, right->tleft);
	Tree* u = numerator_fun(left), * v = denominator_fun(left);
	Tree* w = numerator_fun(right), * x = denominator_fun(right);
	Tree* xx = clone(x), * vv = clone(v);
	Tree* num1 = simplify_RNE_rec(join(u, x, fnc[PROD].ex)), * num2 = simplify_RNE_rec(join(v, w, fnc[PROD].ex));
	Tree* denom = simplify_RNE_rec(join(vv, xx, fnc[PROD].ex)), * num = simplify_RNE_rec(join(num1, num2, fnc[ADD].ex));
	Tree* t = join(num, denom, fnc[DIVID].ex);
	return simplify_RNE_rec(t);
}

static Tree* evaluate_diff(Tree* left, Tree* right)
{
	if (!strcmp(left->value, "0"))
		return (!strcmp(right->value, "0")) ? clone(left) : join(clone(right), NULL, fnc[NEGATIF].ex);
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
	Tree* u = numerator_fun(left), * v = denominator_fun(left);
	Tree* w = numerator_fun(right), * x = denominator_fun(right);
	Tree* xx = clone(x), * vv = clone(v);
	Tree* num1 = simplify_RNE_rec(join(u, x, fnc[PROD].ex)), * num2 = simplify_RNE_rec(join(v, w, fnc[PROD].ex));
	Tree* denom = simplify_RNE_rec(join(vv, xx, fnc[PROD].ex)), * num = simplify_RNE_rec(join(num1, num2, fnc[SUB].ex));
	if (num->tok_type != NEGATIF)
		return simplify_RNE_rec(join(num, denom, fnc[DIVID].ex));
	Tree* tr = join(simplify_RNE_rec(join(num->tleft, denom, fnc[DIVID].ex)), NULL, fnc[NEGATIF].ex);
	clean_noeud(num);
	return tr;
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
		return (Eval(u->tleft) < 0) ? simplify_RNE_rec(join(tr, NULL, fnc[NEGATIF].ex)) : tr;
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

Tree* factorn(long long int val)
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

Tree* trigo_simplify(Tree* u, token tk)
{
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
		string su = Post2in2(u);
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

/* symbolic simplify */

Tree* simplify_integer_power(Tree* v, Tree* w)
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
	else if (v->tok_type == EXP_F)
	{
		v->tleft = join(w, v->tleft, fnc[PROD].ex);
		return simplify(v);
	}
	else if (v->tok_type == PROD)
	{
		Tree* v1 = simplify_power(clone(v->tleft), clone(w)), * v2 = simplify_power(clone(v->tright), w);
		clean_tree(v);
		return join(v1, v2, fnc[PROD].ex);
	}
	else if (v->tok_type == POW)
	{
		Tree* r = v->tleft;
		w = simplify(join(v->tright, w, fnc[PROD].ex));
		clean_noeud(v);
		return join(r, w, fnc[POW].ex);
	}
	else if (v->tok_type == DIVID)
	{
		v->tleft = simplify(join(v->tleft, clone(w), fnc[POW].ex));
		v->tright = simplify(join(v->tright, w, fnc[POW].ex));
		return v;
	}
	else if (w->gtype == ENT && ALG_EXPAND)
		return simplify_integer_power(v, w);
	else if (w->gtype == NEGATION)
	{
		Tree* tr = simplify(join(v, w->tleft, fnc[POW].ex));
		clean_noeud(w);
		if (tr->tok_type == POW)
		{
			if (isdemi(tr->tright) && tr->tleft->gtype == ENT)
				return join(join(clone(tr->tleft), join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex), tr, fnc[PROD].ex);
			Tree* p = simplify(join(tr->tright, NULL, fnc[NEGATIF].ex));
			Tree* r = join(tr->tleft, p, fnc[POW].ex);
			clean_noeud(tr);
			return r;
		}
		if (tr->tok_type == DIVID)
		{
			Tree* r = join(tr->tright, tr->tleft, fnc[DIVID].ex);
			clean_noeud(tr);
			return r;
		}
		return join(tr, join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex);
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
			map L = map_create_prod(f);
			clean_tree(f);
			clean_tree(v);
			Tree* s = new_tree("1"), * q = NULL;
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
	Tree* p1 = p->begin->tr, * q1 = q->begin->tr;
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
		map L = push_front_map(merge(p, q, tk), h->begin->tr);
		h = clear_map(h);
		return (tk == PROD) ? L : simplify_oper_rec(L, tk);
	}
	if (tree_compare(h->begin->tr, p1))
		p = pop_front_map(p);
	else
		q = pop_front_map(q);
	map L = push_front_map(merge(p, q, tk), h->begin->tr);
	h = clear_map(h);
	return L;
}

static map simplify_sum_fct(Tree* u1, Tree* u2)
{
	Tree* v = denominator_fun(u1), * x = denominator_fun(u2);
	bool i = strcmp(v->value, "1"), k = strcmp(x->value, "1");
	clean_tree(v); clean_tree(x);
	if (ALG_EXPAND && (i || k))
	{
		clean_tree(v); clean_tree(x);
		return push_back_map_s(NULL, simplify(rationalize_sum(u1, u2, fnc[ADD].ex)));
	}
	map map_u1 = map_create_prod(u1), map_u2 = map_create_prod(u2);
	Tree* fact_com = NULL;
	mapCell* tmp0 = map_u1->begin, * tmp1 = NULL;
	while (tmp0 != NULL)
	{
		tmp1 = map_u2->begin;
		while (tmp1 != NULL)
		{
			if (tree_compare(tmp1->tr, tmp0->tr) && !isconstant(tmp1->tr))
			{
				fact_com = (fact_com == NULL) ? clone(tmp0->tr) : join(fact_com, clone(tmp0->tr), fnc[PROD].ex);
				clean_tree(tmp1->tr);
				tmp1->tr = new_tree("1");
				clean_tree(tmp0->tr);
				tmp0->tr = new_tree("1");
				break;
			}
			tmp1 = tmp1->next;
		}
		tmp0 = tmp0->next;
	}
	if (fact_com != NULL)
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
		return push_back_map_s(NULL, join(v, fact_com, fnc[PROD].ex));
	}
	map_u1 = clear_map(map_u1);
	map_u2 = clear_map(map_u2);
	return push_back_map(push_back_map(NULL, u1), u2);
}

static map simplify_oper_rec(map L, token tk)
{
	if (L->length == 1)
		return L;
	Tree* u1 = (L->begin->tr), * u2 = (L->end->tr);
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
			L = push_back_map_s(L, p);
			return L;
		}
		if (!strcmp(u1->value, nb) || !strcmp(u2->value, nb))
		{
			if (!strcmp(u1->value, nb))
				L = pop_front_map(L);
			else
				L = pop_back_map(L);
			return L;
		}
		if (tk == PROD)
		{
			if (tree_compare(base(u1), base(u2)))
			{
				Tree* s = simplify(join(clone(base(u1)), join(exponent(u1), exponent(u2), fnc[ADD].ex), fnc[POW].ex));
				L = clear_map(L);
				map q = (!strcmp(s->value, nb)) ? NULL : push_back_map(L, s);
				clean_tree(s);
				return q;
			}
			if (u1->tok_type == EXP_F && u2->tok_type == EXP_F)
			{
				L = push_back_map_s(clear_map(L), simplify(join(join(clone(u1->tleft), clone(u2->tleft), fnc[ADD].ex), NULL, fnc[EXP_F].ex)));
				return L;
			}
		}
		if (tk == ADD)
		{
			if (tree_compare(u1, u2))
			{
				L = push_back_map_s(clear_map(L), simplify(join(new_tree("2"), clone(u1), fnc[PROD].ex)));
				return L;
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
			map l = push_back_map(push_back_map(NULL, u2), u1);
			L = clear_map(L);
			return l;
		}
		return L;
	}
	else if (L->length == 2 && (u1tok == tk || u1tok == tok || u2tok == tk || u2tok == tok))
	{
		map p = (tk == PROD) ? map_create_prod(u1) : map_create_add(u1), q = (tk == PROD) ? map_create_prod(u2) : map_create_add(u2);
		L = clear_map(L);
		return merge(p, q, tk);
	}
	else if (isconstant(u1) && isconstant(L->begin->next->tr))
	{
		Tree* p = simplify_RNE(join(clone(u1), clone(L->begin->next->tr), fnc[tk].ex));
		L = push_front_map(pop_front_map(pop_front_map(L)), p);
		clean_tree(p);
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
		if (!strcmp(tmp->tr->value, fnc[UNDEF].ex) || (tk == PROD && !strcmp(tmp->tr->value, "0")))
		{
			Tree* t = clone(tmp->tr);
			L = clear_map(L);
			return t;
		}
		tmp = tmp->next;
	}
	map v = simplify_oper_rec(L, tk);
	if (v == NULL)
		return new_tree((tk == PROD) ? "1" : "0");
	return construct(fnc[tk].ex, &v);
}

static Tree* construct(const char* op, map* L)
{
	mapCell* tmp = (*L)->begin;
	Tree* tr = NULL;
	while (tmp != NULL)
	{
		tr = (tr == NULL) ? clone(tmp->tr) : join(tr, clone(tmp->tr), op);
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
			if (q > 0)
				return new_tree("1");
			return join(new_tree("1"), NULL, fnc[NEGATIF].ex);
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
		Tree* q = join(simplify(clone(k ? u->tleft->tleft : u->tleft)), NULL, fnc[LN_F].ex), * w = join(k ? clone(u->tleft->tright) : new_tree("10"), NULL, fnc[LN_F].ex);
		clean_tree(u);
		Tree* v = simplify_ln(q);
		clean_tree(q);
		if (v->tok_type == UNDEF)
		{
			clean_tree(w);
			return v;
		}
		return join(v, w, fnc[DIVID].ex);
	}
	if (tk == ABS_F)
	{
		Tree* t = absolute_value(simplify(u->tleft));
		clean_noeud(u);
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
		Tree* v = join(clone(u->tleft), NULL, fnc[tk - 1].ex), * w = join(clone(u->tleft), NULL, fnc[tk - 2].ex);
		clean_tree(u);
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
			if (strcmp(dn->value, "0") && strcmp(dd->value, "0"))
			{
				clean_tree(dd); clean_tree(dn);
				Tree* tr = poly_simp(polycoeffs(u->tleft, vr), polycoeffs(u->tright, vr), vr);
				free(vr);
				clean_tree(u);
				return tr;
			}
			clean_tree(dn); clean_tree(dd);
		}
		free(vr);
	}
	if (tk == ADD || tk == SUB || tk == PROD || tk == DIVID)
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
				Tree* z = join(clone(tr->tleft), join(clone(cf->begin->tr), join(clone(cf->end->tr), new_tree(fnc[IMAGE].ex), fnc[PROD].ex), fnc[SUB].ex), fnc[PROD].ex);
				Tree* o = join(join(clone(cf->begin->tr), new_tree("2"), fnc[POW].ex), join(clone(cf->end->tr), new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
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
	DList vrs = NULL;
	vrs = getvars(r, vrs);
	if (vrs == NULL)
		vrs = getvars(s, vrs);
	if (vrs != NULL && ispoly(r, vrs->begin->value) && ispoly(s, vrs->begin->value))
	{
		Tree* dr = degree_sv(r, vrs->begin->value), * ds = degree_sv(s, vrs->begin->value);
		int r1 = (int)Eval(dr), s1 = (int)Eval(ds);
		clean_tree(dr); clean_tree(ds);
		if (ismonomial(r, vrs->begin->value) && ismonomial(s, vrs->begin->value))
		{
			Tree* a = coefficient_gpe(r, vrs->begin->value, r1), * b = coefficient_gpe(s, vrs->begin->value, s1);
			Tree* g = PGCD(a, b);
			vrs = clear_dlist(vrs);
			if (strcmp(g->value, "1"))
			{
				s = simplify(join(s, clone(g), fnc[DIVID].ex));
				r = simplify(join(r, clone(g), fnc[DIVID].ex));
				dr = simplify(join(g, join(clone(s), clone(r), fnc[PROD].ex), fnc[PROD].ex));
				m = simplify(join(m, s, fnc[PROD].ex));
				n = simplify(join(n, r, fnc[PROD].ex));
				return join(join(m, n, op), dr, fnc[DIVID].ex);
			}
			clean_tree(g);
			return NULL;
		}
		if (r1 * s1 > 0)
		{
			map coef_r = polycoeffs(r, vrs->begin->value), coef_s = polycoeffs(s, vrs->begin->value);
			clean_tree(r); clean_tree(s);
			map GCD = poly_gcd(coef_r, coef_s);
			map quot_r = poly_quotient(coef_r, GCD, INT_F), quot_s = poly_quotient(coef_s, GCD, INT_F);
			Tree* qr = polyreconstitute(&quot_r, vrs->begin->value), * qs = polyreconstitute(&quot_s, vrs->begin->value);
			Tree* g = polyreconstitute(&GCD, vrs->begin->value);
			coef_r = clear_map(coef_r); coef_s = clear_map(coef_s);
			vrs = clear_dlist(vrs);
			dr = simplify(join(g, join(clone(qs), clone(qr), fnc[PROD].ex), fnc[PROD].ex));
			m = simplify(join(m, qs, fnc[PROD].ex));
			n = simplify(join(n, qr, fnc[PROD].ex));
			return join(join(m, n, op), dr, fnc[DIVID].ex);
		}
	}
	if (vrs != NULL)
		vrs = clear_dlist(vrs);
	return NULL;
}

static Tree* rationalize_sum(Tree* u, Tree* v, const char* op)
{
	Tree* m = numerator_fun(u), * r = denominator_fun(u);
	Tree* n = numerator_fun(v), * s = denominator_fun(v);
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
	if (r->gtype == ENT && s->gtype == ENT)
	{
		char* p = gcd(r->value, s->value);
		if (strcmp(p, "1"))
		{
			if (greater(r->value, s->value))
			{
				clean_tree(s);
				n = simplify(join(new_tree(p), n, fnc[PROD].ex));
				free(p);
				return join(join(m, n, op), r, fnc[DIVID].ex);
			}
			clean_tree(r);
			m = simplify(join(new_tree(p), m, fnc[PROD].ex));
			free(p);
			return join(join(m, n, op), s, fnc[DIVID].ex);
		}
		free(p);
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

Tree* contract_exp_rules(Tree* u)
{
	Tree* v = expand_main_op(u);
	if (v->tok_type == POW && v->tleft->tok_type == EXP_F)
	{
		Tree* p = join(clone(v->tright), clone(v->tleft->tleft), fnc[PROD].ex);
		Tree* s = contract_exp_rules(p);
		clean_tree(p); clean_tree(v);
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
			Tree* q = contract_exp_rules(tmp->tr);
			clean_tree(tmp->tr);
			tmp->tr = q;
			if (tmp->tr->tok_type == EXP_F)
				s = simplify(join(s, clone(tmp->tr->tleft), fnc[ADD].ex));
			else
				p = simplify(join(p, clone(tmp->tr), fnc[PROD].ex));
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
	token tk = u->tok_type;
	if (ADD <= tk && tk <= POW)
		return contract_exp_rules(u);
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
	if (tk == PROD && u->tleft->gtype == ENT)
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
	if (v->tok_type == ADD || v->tok_type == SUB)
	{
		map L = map_create_add(v);
		Tree* p = NULL, * s = NULL;
		mapCell* item = L->begin;
		while (item != NULL)
		{
			Tree* q = contract_ln_rules(item->tr);
			clean_tree(item->tr);
			item->tr = q;
			if (item->tr->tok_type == LN_F)
				s = (s == NULL) ? clone(item->tr->tleft) : join(s, clone(item->tr->tleft), fnc[PROD].ex);
			else if (item->tr->tok_type == NEGATIF && item->tr->tleft->tok_type == LN_F)
			{
				Tree* w = join(new_tree("1"), clone(item->tr->tleft->tleft), fnc[DIVID].ex);
				s = (s == NULL) ? w : join(s, w, fnc[PROD].ex);
			}
			else if (item->tr->tok_type == PROD && item->tr->tleft->tok_type == NEGATIF && !strcmp(item->tr->tleft->tleft->value, "1") && item->tr->tright->tok_type == LN_F)
			{
				Tree* w = join(new_tree("1"), clone(item->tr->tright->tleft), fnc[DIVID].ex);
				s = (s == NULL) ? w : join(s, w, fnc[PROD].ex);
			}
			else if (strcmp(item->tr->value, "0"))
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

Tree* expand_ln_rules(Tree* u)
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
		map cf = polycoeffs(u->tright, fnc[IMAGE].ex);
		Tree* a = join(join(clone(cf->begin->tr), new_tree("2"), fnc[POW].ex), join(clone(cf->end->tr), new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
		cf = clear_map(cf);
		return simplify(a);
	}
	return join(u, NULL, fnc[ABS_F].ex);
}

Tree* Contract_pow(Tree* v)
{
	if (v->tok_type == ADD || v->tok_type == SUB || v->tok_type == POW)
	{
		Tree* tr = join(Contract_pow(v->tleft), Contract_pow(v->tright), v->value);
		clean_noeud(v);
		return tr;
	}
	else if (v->tok_type == PROD || v->tok_type == DIVID)
	{
		map L = map_create(v), q = NULL, s = NULL, p = NULL;
		clean_tree(v);
		mapCell* item = L->begin;
		while (item != NULL)
		{
			if (item->tr->tok_type == POW)
			{
				int index = -1;
				if (q != NULL)
				{
					mapCell* tmp = q->begin, * tmp1 = s->begin;
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
				p = push_back_map(p, item->tr);
			item = item->next;
		}
		L = clear_map(L);
		if (q != NULL)
		{
			mapCell* tmp = q->begin, * tmp1 = s->begin;
			while (tmp != NULL)
			{
				p = push_back_map_s(p, join(clone(tmp1->tr), clone(tmp->tr), fnc[POW].ex));
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

Tree* degree_monomial_sv(Tree* u, const char* x)
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
			Tree* f = degree_monomial_sv(tmp->tr, x);
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
			Tree* a = clone(tmp->tr);
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
		if (strcmp(tmp->tr->value, "0"))
		{
			Tree* v = clone(tmp->tr);
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

map polynomial_division(map* divd, map* divr, map* rem)
{
	map tmp = NULL, quot = NULL;
	Tree* a = NULL;
	if ((*divd)->length < (*divr)->length)
		return polynomial_division(divr, divd, rem);
	bool z = true;
	while ((*divd)->length >= (*divr)->length)
	{
		a = simplify(join(clone((*divd)->begin->tr), clone((*divr)->begin->tr), fnc[DIVID].ex));
		mapCell* t = (*divr)->begin;
		while (t != NULL)
		{
			tmp = push_back_map_s(tmp, simplify(join(clone(a), clone(t->tr), fnc[PROD].ex)));
			t = t->next;
		}
		mapCell* celdivd = (*divd)->begin, * celtmp = tmp->begin;
		while (celdivd != NULL && celtmp != NULL)
		{
			celdivd->tr = simplify(join(celdivd->tr, clone(celtmp->tr), fnc[SUB].ex));
			celdivd = celdivd->next;
			celtmp = celtmp->next;
		}
		quot = push_back_map_s(quot, a);
		tmp = clear_map(tmp);
		z = true;
		(*divd) = pop_front_map(*divd);
		if ((*divd) == NULL)
			break;
		celdivd = (*divd)->begin;
		while (celdivd != NULL)
		{
			if (strcmp(celdivd->tr->value, "0"))
			{
				z = false;
				break;
			}
			celdivd = celdivd->next;
		}
		if (z && (*divd) != NULL)
		{
			for (int i = 0; i < (*divd)->length - 1; i++)
				quot = push_back_map_s(quot, new_tree("0"));
			(*divd) = clear_map(*divd);
			break;
		}
	}
	if ((*divd) == NULL)
		(*divd) = push_back_map_s(*divd, new_tree("0"));
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
	if (u->length == 1 && !strcmp(u->begin->tr->value, "0") && v->length == 1 && !strcmp(v->begin->tr->value, "0"))
		return push_back_map_s(NULL, new_tree("1"));
	map U = NULL, V = NULL;
	if (v->length > u->length)
	{
		U = clone_map(v);
		V = clone_map(u);
	}
	else
	{
		U = clone_map(u);
		V = clone_map(v);
	}
	while (V->length > 1 || strcmp(V->begin->tr->value, "0"))
	{
		map R = poly_quotient(U, V, REMAINDER_F);
		U = clear_map(U);
		U = V;
		V = R;
	}
	V = clear_map(V);
	Tree* lcr = clone(U->begin->tr);
	mapCell* tmp = U->begin;
	while (tmp != NULL)
	{
		tmp->tr = simplify(join(tmp->tr, clone(lcr), fnc[DIVID].ex));
		tmp = tmp->next;
	}
	clean_tree(lcr);
	return U;
}

Tree* poly_simp(map u, map v, const char* x)
{
	map pgcd = poly_gcd(u, v);
	if (pgcd->length > 1 || (pgcd->length == 1 && strcmp(pgcd->begin->tr->value, "1")))
	{
		map qn = poly_quotient(u, pgcd, INT_F), qd = poly_quotient(v, pgcd, INT_F);
		pgcd = clear_map(pgcd); u = clear_map(u); v = clear_map(v);
		Tree* ql = polyreconstitute(&qn, x), * qr = polyreconstitute(&qd, x);
		if (!strcmp(qr->value, "1"))
		{
			clean_tree(qr);
			return ql;
		}
		return join(ql, qr, fnc[DIVID].ex);
	}
	pgcd = clear_map(pgcd);
	return join(polyreconstitute(&u, x), polyreconstitute(&v, x), fnc[DIVID].ex);
}

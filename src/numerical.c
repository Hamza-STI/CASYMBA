#include "numerical.h"

Number create(int signe, const char* nbr)
{
	Number number = { signe, strdup(nbr) };
	return number;
}

void free_Number(Number nbr)
{
	free(nbr.nombre);
}

void zero_untile(char* a)
{
	int len_a = strlen(a);
	int i = 0, k = len_a - 1, pos = 0;
	while (i < len_a && a[i] == '0')
		i++;
	if (a[i] == '.')
		i--;
	while (k > i && a[k] == '0')
		k--;
	if (a[k] == '.')
		k--;
	for (int j = i; j <= k; j++)
		a[pos++] = a[j];
	if (pos == 0)
		a[pos++] = '0';
	a[pos] = '\0';
}

static bool greater(const char* a, const char* b)
{
	char* c = strchr(a, '.'), * d = strchr(b, '.');
	int len_c = (c == NULL) ? 0 : strlen(c), len_d = (d == NULL) ? 0 : strlen(d);
	int len_a = strlen(a) - len_c, len_b = strlen(b) - len_d;
	int n = (len_c < len_d) ? len_c : len_d;
	if (len_a != len_b)
		return len_a > len_b;
	for (int i = 0; i < len_a + n; i++)
		if (a[i] != b[i])
			return a[i] > b[i];
	return false;
}

char* new_value(const char* a, unsigned size_int_a, unsigned size_dec_a, unsigned new_size_int, unsigned new_size_dec)
{
	int k = strlen(a);
	if (k == (int)(new_size_int + new_size_dec))
		return strdup(a);
	int length = new_size_int - size_int_a, s = new_size_int + new_size_dec;
	char* ret = malloc(s + 1);
	memset(ret, '0', s * sizeof(char));
	memcpy(ret + length, a, k);
	if (new_size_dec && !size_dec_a)
		ret[length + k] = '.';
	ret[s] = '\0';
	return ret;
}

static int sub_cc(char a, char b, int* retenue)
{
	int r = a - '0', s = b - '0' + *retenue;
	*retenue = (r < s) ? 1 : 0;
	return (r - s + 10) % 10;
}

static int add_cc(char a, char b, int* retenue)
{
	int w = a - '0' + b - '0' + *retenue;
	*retenue = (w >= 10) ? 1 : 0;
	return w % 10;
}

static Number adds(Number left, Number right, int op)
{
	char* c = strchr(left.nombre, '.'), * d = strchr(right.nombre, '.');
	int len_c = (c == NULL) ? 0 : strlen(c), len_d = (d == NULL) ? 0 : strlen(d);
	int len_a = strlen(left.nombre) - len_c, len_b = strlen(right.nombre) - len_d;
	int m = max(len_a, len_b), n = max(len_c, len_d), pos = 0, retenue = 0;
	char clc[50] = { 0 };
	char* new_a = new_value(left.nombre, len_a, len_c, m, n), * new_b = new_value(right.nombre, len_b, len_d, m, n);
	for (int i = m + n - 1; i >= 0; --i)
	{
		if (new_a[i] == '.')
			clc[pos++] = '.';
		else
			clc[pos++] = '0' + ((op == 1) ? add_cc(new_a[i], new_b[i], &retenue) : sub_cc(new_a[i], new_b[i], &retenue));
	}
	if (op == 1 && retenue == 1)
		clc[pos] = '1';
	else
		pos--;
	while (clc[pos] == '0' && pos > 1)
		pos--;
	if (clc[pos] == '.')
		pos++;
	char ret[50] = { 0 };
	for (int i = pos; i >= 0; --i)
		ret[pos - i] = clc[i];
	ret[pos + 1] = '\0';
	free(new_a); free(new_b);
	zero_untile(ret);
	return create(1, ret);
}

Number sub(Number left, Number right)
{
	if (!strcmp(left.nombre, right.nombre))
	{
		Number resultat = { 1,strdup("0") };
		return resultat;
	}
	if (greater(right.nombre, left.nombre))
	{
		Number resultat = sub(right, left);
		resultat.signe *= -1;
		return resultat;
	}
	return adds(left, right, -1);
}

Number add(Number left, Number right)
{
	return adds(left, right, 1);
}

Number prod(Number left, Number right)
{
	char* c = strchr(left.nombre, '.'), * d = strchr(right.nombre, '.');
	int len_a = strlen(left.nombre), len_b = strlen(right.nombre), len_c = (c == NULL) ? 0 : strlen(c) - 1, len_d = (d == NULL) ? 0 : strlen(d) - 1;
	int pos = 0, retenue = 0, w = 0, s = 0;
	char clc[50] = { 0 }, n_clc[50] = { 0 }, tmp[50] = { 0 };
	for (int i = len_a - 1; i >= 0; i--)
	{
		if (left.nombre[i] != '.')
		{
			pos = 0;
			retenue = 0;
			for (int k = 0; k < s; ++k)
				clc[pos++] = '0';
			s++;
			for (int k = len_b - 1; k >= 0; k--)
			{
				if (right.nombre[k] != '.')
				{
					w = ((left.nombre[i] - '0') * (right.nombre[k] - '0')) + retenue;
					retenue = w / 10;
					clc[pos++] = '0' + (w % 10);
				}
			}
			if (retenue > 0)
				clc[pos] = '0' + retenue;
			else
				pos--;
			for (int k = 0; k <= pos; k++)
				n_clc[k] = clc[pos - k];
			if (strlen(tmp) == 0)
				strcpy(tmp, n_clc);
			else
			{
				Number r = create(1, n_clc), s = create(1, tmp);
				Number t = add(r, s);
				strcpy(tmp, t.nombre);
				free_Number(r); free_Number(s); free_Number(t);
			}
		}
	}
	pos = 0;
	s = strlen(tmp);
	w = len_c + len_d;
	if (s <= w)
	{
		int k = max(s - w, w - s) + 2;
		char* ch = malloc(k * sizeof(char)), t[50];
		memset(ch, '0', k * sizeof(char));
		ch[k - 1] = '\0';
		snprintf(t, 50, "%s%s", ch, tmp);
		s = strlen(t);
		strcpy(tmp, t);
		free(ch);
	}
	char ret[50] = { 0 };
	for (int i = 0; i < s; ++i)
	{
		ret[pos++] = tmp[i];
		if (s - (i + 1) == w)
			ret[pos++] = '.';
	}
	ret[pos] = '\0';
	zero_untile(ret);
	return create(1, ret);
}

static int divid_quot(Number denom, char* tmp)
{
	int k;
	for (k = 1; k < 10; k++)
	{
		char w[2] = { '0' + k, '\0' };
		Number nbr = create(1, w);
		Number n = prod(denom, nbr);
		bool sup = greater(n.nombre, tmp);
		free_Number(n); free_Number(nbr);
		if (sup > 0)
			break;
	}
	k--;
	char u[2] = { '0' + k, '\0' };
	Number nbr_1 = create(1, u), nbr_2 = create(1, tmp);
	Number m = prod(denom, nbr_1);
	Number v = sub(nbr_2, m);
	memset(tmp, 0, 50 * sizeof(char));
	strcpy(tmp, v.nombre);
	free_Number(v); free_Number(m); free_Number(nbr_1); free_Number(nbr_2);
	return k;
}

Number int_divid(Number num, Number denom, Number* rem)
{
	int len_a = strlen(num.nombre), len_b = strlen(denom.nombre), pos = 0, p = 0;
	char tmp[50] = { 0 }, quot[50] = { 0 };
	for (int i = 0; i < len_b; ++i)
	{
		if (i == len_a)
		{
			++pos;
			break;
		}
		tmp[pos++] = num.nombre[i];
	}
	do {
		quot[p++] = '0' + divid_quot(denom, tmp);
		if (pos < len_a)
			tmp[!strcmp(tmp, "0") ? 0 : strlen(tmp)] = num.nombre[pos];
		++pos;
	} while (pos <= len_a);
	zero_untile(quot);
	if (strlen(tmp) == 0)
		tmp[0] = '0';
	zero_untile(tmp);
	if (rem != NULL)
		(*rem).nombre = strdup(tmp);
	return create(1, quot);
}

Number divid(Number num, Number denom)
{
	char* c = strchr(num.nombre, '.'), * d = strchr(denom.nombre, '.');
	int len_c = (c == NULL) ? 0 : strlen(c) - 1, len_d = (d == NULL) ? 0 : strlen(d) - 1;
	int len_a = strlen(num.nombre), len_b = strlen(denom.nombre), pos = 0, prec = 0, p = 0;
	char new_a[50] = { 0 }, new_b[50] = { 0 }, tmp[50] = { 0 }, quot[50] = { 0 };
	bool digit = false;
	if (len_d > 0)
	{
		if (!len_c)
		{
			strcpy(new_a, num.nombre);
			for (int i = 0; i < len_d; ++i)
				new_a[len_a + i] = '0';
		}
		else
		{
			pos = 0;
			for (int i = 0; i < len_a; ++i)
			{
				if (num.nombre[i] == '.')
					digit = true;
				else if (digit)
				{
					if (len_d == 0)
						new_a[pos++] = '.';
					new_a[pos++] = num.nombre[i];
					len_d--;
				}
				else
					new_a[pos++] = num.nombre[i];
			}
			while (len_d > 0)
			{
				new_a[pos++] = '0';
				len_d--;
			}
		}
		pos = 0;
		for (int i = 0; i < len_b; ++i)
			if (denom.nombre[i] != '.')
				new_b[pos++] = denom.nombre[i];
	}
	else
	{
		strcpy(new_a, num.nombre);
		strcpy(new_b, denom.nombre);
	}
	zero_untile(new_a); zero_untile(new_b);
	pos = 0;
	len_b = strlen(new_b);
	len_a = strlen(new_a);
	digit = false;
	for (int i = 0; i < len_b; ++i)
	{
		if (new_a[i] == '.' || i == len_a)
			break;
		tmp[pos] = new_a[i];
		++pos;
	}
	while (prec < 15)
	{
		Number n_b = create(1, new_b);
		quot[p++] = '0' + divid_quot(n_b, tmp);
		free_Number(n_b);
		if (!strcmp(tmp, "0") && pos >= len_a)
			break;
		if (((pos < len_a && new_a[pos] == '.') || pos == len_a) && !digit)
		{
			digit = true;
			++pos;
			quot[p++] = '.';
		}
		else if (digit)
			prec++;
		tmp[!strcmp(tmp, "0") ? 0 : strlen(tmp)] = (pos >= len_a) ? '0' : new_a[pos];
		++pos;
	}
	return create(num.signe * denom.signe, quot);
}

Number gcd(Number num, Number denom)
{
	if (!strcmp(num.nombre, "1") || !strcmp(denom.nombre, "1"))
		return create(1, "1");
	if (!strcmp(num.nombre, denom.nombre))
		return create(num.signe, num.nombre);
	if (greater(denom.nombre, num.nombre))
		return gcd(denom, num);
	Number rem, d = create(denom.signe, denom.nombre);
	Number q = int_divid(num, denom, &rem);
	free_Number(q);
	while (strcmp(rem.nombre, "0"))
	{
		Number tmp;
		Number q1 = int_divid(d, rem, &tmp);
		free_Number(d);
		d = create(rem.signe, rem.nombre);
		free_Number(q1); free_Number(rem);
		rem = tmp;
	}
	free_Number(rem);
	return d;
}

Number Exponentiel(Number x)
{
	char resultat[50] = "1", terme[50] = { 0 };
	strcpy(terme, x.nombre);
	const char* l[] = { "1", "2", "6", "24", "120", "720", "5040", "40320", "362880", "3628800", "39916800", "479001600", "6227020800", "87178291200", "1307674368000" };
	for (int i = 1; i < 15; i++)
	{
		Number denom = create(1, l[i - 1]), puissance = create(1, terme), rst = create(1, resultat);
		Number a = divid(puissance, denom), b = prod(puissance, x);
		memset(terme, 0, 50 * sizeof(char));
		strcpy(terme, b.nombre);
		Number c = (x.signe == -1 && (int)(i / 2) != (i / 2)) ? sub(rst, a) : add(rst, a);
		memset(resultat, 0, 50 * sizeof(char));
		strcpy(resultat, c.nombre);
		free_Number(a); free_Number(b); free_Number(c); free_Number(rst); free_Number(denom); free_Number(puissance);
	}
	return create(1, resultat);
}

Number Logarithme(Number x)
{
	char resultat[50] = "0";
	Number c = create(1, "1");
	Number terme = sub(x, c);
	const char* l[] = { "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15" };
	strcpy(resultat, terme.nombre);
	free_Number(c);
	for (int i = 2; i < 14; i++)
	{
		c = create(1, l[i - 2]);
		Number puissance = ExponentiationRapide(terme, c);
		Number a = divid(puissance, c);
		free_Number(c);
		c = create(1, resultat);
		Number s = (i / 2 == (int)(i / 2)) ? add(c, a) : sub(c, a);
		memset(resultat, 0, 50 * sizeof(char));
		strcpy(resultat, s.nombre);
		free_Number(a); free_Number(c); free_Number(s); free_Number(puissance);
	}
	Number result = create(terme.signe, resultat);
	free_Number(terme);
	return result;
}

Number ExponentiationRapide(Number bas, Number exposant)
{
	if (!strcmp(exposant.nombre, "0"))
		return create(1, "1");
	if (strchr(exposant.nombre, '.'))
	{
		Number cln = Logarithme(bas);
		Number p = prod(exposant, cln);
		Number resultat = Exponentiel(p);
		free_Number(cln); free_Number(p);
		return resultat;
	}
	Number reste, denom = create(1, "2");
	Number quot = int_divid(exposant, denom, &reste);
	free_Number(denom);
	if (!strcmp(reste.nombre, "0"))
	{
		Number moitie = ExponentiationRapide(bas, quot);
		Number resultat = prod(moitie, moitie);
		free_Number(quot); free_Number(moitie); free_Number(reste);
		return resultat;
	}
	else
	{
		denom = create(1, "1");
		Number s = sub(exposant, denom);
		free_Number(denom); free_Number(quot); free_Number(reste);
		denom = create(1, "2");
		quot = int_divid(s, denom, &reste);
		free_Number(s); free_Number(denom);
		Number moitie = ExponentiationRapide(bas, quot);
		Number p = prod(moitie, moitie);
		Number resultat = prod(bas, p);
		free_Number(p); free_Number(quot); free_Number(moitie); free_Number(reste);
		return resultat;
	}
}

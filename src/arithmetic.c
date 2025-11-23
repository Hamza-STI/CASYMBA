#include "includes.h"

Number create(int signe, const char* nbr)
{
	return (Number) { signe, strdup(nbr) };
}

void free_Number(Number nbr)
{
	free(nbr.nombre);
}

#define BUF 256
#define MAX_PREC 11
#define ITER 15

static void expStrings(const char* x, char* result);
static void lnStrings(const char* x, char* result);

void trim_str(char* s) {
	if (!s || !*s) return;
	while (*s == ' ') memmove(s, s + 1, strlen(s));
	int i = 0;
	while (s[i] == '0' && s[i + 1] != '\0' && s[i + 1] != '.') i++;
	if (i) memmove(s, s + i, strlen(s + i) + 1);
	char* dot = strchr(s, '.');
	if (dot) {
		int end = strlen(s) - 1;
		while (end > (dot - s) && s[end] == '0') s[end--] = '\0';
		if (end == (dot - s)) s[end] = '\0';
	}
}

static int cmp_intstr(const char* a, const char* b) {
	while (*a == '0' && *(a + 1) != '\0') a++;
	while (*b == '0' && *(b + 1) != '\0') b++;
	int la = strlen(a), lb = strlen(b);
	if (la < lb) return -1;
	if (la > lb) return 1;
	return strcmp(a, b);
}

int compareStrings(const char* a_in, const char* b_in) {
	static char a[BUF], b[BUF];
	int ia = 0, ib = 0;

	for (int i = 0; a_in[i] && ia < BUF - 1; i++) {
		if ((a_in[i] >= '0' && a_in[i] <= '9') || a_in[i] == '.' || a_in[i] == '-' || a_in[i] == '+')
			a[ia++] = a_in[i];
	}
	a[ia] = '\0';

	for (int i = 0; b_in[i] && ib < BUF - 1; i++) {
		if ((b_in[i] >= '0' && b_in[i] <= '9') || b_in[i] == '.' || b_in[i] == '-' || b_in[i] == '+')
			b[ib++] = b_in[i];
	}
	b[ib] = '\0';

	int signA = 1, signB = 1;
	char* A = a, * B = b;

	if (*A == '-') { signA = -1; A++; }
	else if (*A == '+') A++;

	if (*B == '-') { signB = -1; B++; }
	else if (*B == '+') B++;

	if (signA != signB)
		return (signA < signB) ? -1 : 1;

	static char Ai[BUF], Af[BUF], Bi[BUF], Bf[BUF];
	int Ai_len = 0, Af_len = 0, Bi_len = 0, Bf_len = 0;

	char* dotA = strchr(A, '.');
	if (dotA) {
		Ai_len = dotA - A;
		memcpy(Ai, A, Ai_len);
		Ai[Ai_len] = '\0';
		strcpy(Af, dotA + 1);
		Af_len = strlen(Af);
	}
	else {
		strcpy(Ai, A);
		Ai_len = strlen(Ai);
		Af[0] = '\0';
		Af_len = 0;
	}

	char* dotB = strchr(B, '.');
	if (dotB) {
		Bi_len = dotB - B;
		memcpy(Bi, B, Bi_len);
		Bi[Bi_len] = '\0';
		strcpy(Bf, dotB + 1);
		Bf_len = strlen(Bf);
	}
	else {
		strcpy(Bi, B);
		Bi_len = strlen(Bi);
		Bf[0] = '\0';
		Bf_len = 0;
	}
	int ziA = 0; while (Ai[ziA] == '0' && Ai[ziA + 1]) ziA++;
	if (ziA) memmove(Ai, Ai + ziA, strlen(Ai + ziA) + 1);

	int ziB = 0; while (Bi[ziB] == '0' && Bi[ziB + 1]) ziB++;
	if (ziB) memmove(Bi, Bi + ziB, strlen(Bi + ziB) + 1);
	while (Af_len > 0 && Af[Af_len - 1] == '0') Af[--Af_len] = '\0';
	while (Bf_len > 0 && Bf[Bf_len - 1] == '0') Bf[--Bf_len] = '\0';
	if (strlen(Ai) < strlen(Bi)) return (signA == 1) ? -1 : 1;
	if (strlen(Ai) > strlen(Bi)) return (signA == 1) ? 1 : -1;

	int cmp = strcmp(Ai, Bi);
	if (cmp != 0) return (cmp < 0) ? -1 * signA : 1 * signA;
	int maxf = (Af_len > Bf_len ? Af_len : Bf_len);
	for (int i = 0; i < maxf; i++) {
		char ca = (i < Af_len) ? Af[i] : '0';
		char cb = (i < Bf_len) ? Bf[i] : '0';
		if (ca < cb) return (signA == 1) ? -1 : 1;
		if (ca > cb) return (signA == 1) ? 1 : -1;
	}

	return 0;
}

static void reduceDecimals(char* s, int prec) {
	if (!s) return;
	if (prec < 0) { trim_str(s); return; }
	char* p = s;
	if (*p == '-') { p++; }
	char* dot = strchr(p, '.');
	if (!dot) {
		return;
	}
	int frac_len = strlen(dot + 1);
	if (frac_len <= prec) {
		trim_str(s);
		return;
	}
	int cut_idx = (int)(dot - s) + 1 + prec;
	char next = s[cut_idx];
	if (next >= '5' && next <= '9') {
		int i = cut_idx - 1;
		while (i >= 0) {
			if (s[i] == '.') { i--; continue; }
			if (s[i] == '-') break;
			if (s[i] < '0' || s[i] > '9') { i--; continue; }
			if (s[i] < '9') { s[i] = s[i] + 1; break; }
			s[i] = '0';
			i--;
		}
		if (i < 0 || s[i] == '-') {
			if (s[0] == '-') {
				int len = strlen(s);
				if (len + 1 < BUF) {
					memmove(s + 2, s + 1, len);
					s[1] = '1';
				}
			}
			else {
				int len = strlen(s);
				if (len + 1 < BUF) {
					memmove(s + 1, s, len + 1);
					s[0] = '1';
				}
			}
		}
	}
	s[cut_idx] = '\0';
	trim_str(s);
}

static void addStrings(const char* a, const char* b, char* result) {
	static char A[BUF], B[BUF], R[BUF];
	strncpy(A, a, BUF - 1); A[BUF - 1] = '\0';
	strncpy(B, b, BUF - 1); B[BUF - 1] = '\0';
	char* dotA = strchr(A, '.');
	char* dotB = strchr(B, '.');
	static char intA[BUF], intB[BUF], fracA[BUF], fracB[BUF];
	if (dotA) {
		int la = dotA - A;
		if (la >= BUF) { strcpy(result, "NaN"); return; }
		strncpy(intA, A, la); intA[la] = '\0';
		strncpy(fracA, dotA + 1, BUF - 1); fracA[BUF - 1] = '\0';
	}
	else { strncpy(intA, A, BUF - 1); intA[BUF - 1] = '\0'; fracA[0] = '\0'; }

	if (dotB) {
		int lb = dotB - B;
		if (lb >= BUF) { strcpy(result, "NaN"); return; }
		strncpy(intB, B, lb); intB[lb] = '\0';
		strncpy(fracB, dotB + 1, BUF - 1); fracB[BUF - 1] = '\0';
	}
	else { strncpy(intB, B, BUF - 1); intB[BUF - 1] = '\0'; fracB[0] = '\0'; }
	int la_frac = strlen(fracA), lb_frac = strlen(fracB);
	int fmax = la_frac > lb_frac ? la_frac : lb_frac;
	if (fmax >= BUF / 2) { strcpy(result, "NaN"); return; }
	while ((int)strlen(fracA) < fmax) strcat(fracA, "0");
	while ((int)strlen(fracB) < fmax) strcat(fracB, "0");
	int carry = 0;
	int ri = 0;
	int maxIntLen = (int)strlen(intA) > (int)strlen(intB) ? strlen(intA) : strlen(intB);
	if (maxIntLen + fmax + 4 >= BUF) { strcpy(result, "NaN"); return; }
	for (int i = fmax - 1; i >= 0; --i) {
		int da = (i < (int)strlen(fracA) ? fracA[i] - '0' : 0);
		int db = (i < (int)strlen(fracB) ? fracB[i] - '0' : 0);
		int s = da + db + carry;
		R[ri++] = '0' + (s % 10);
		carry = s / 10;
	}
	int frac_count = ri;
	int iA = strlen(intA) - 1, iB = strlen(intB) - 1;
	while (iA >= 0 || iB >= 0 || carry) {
		int da = (iA >= 0 ? intA[iA] - '0' : 0);
		int db = (iB >= 0 ? intB[iB] - '0' : 0);
		int s = da + db + carry;
		R[ri++] = '0' + (s % 10);
		carry = s / 10;
		iA--; iB--;
	}
	int pos = 0;
	int totalDigits = ri;
	for (int k = totalDigits - 1; k >= frac_count; --k) result[pos++] = R[k];
	if (frac_count > 0) {
		result[pos++] = '.';
		for (int k = frac_count - 1; k >= 0; --k) result[pos++] = R[k];
	}
	result[pos] = '\0';
	trim_str(result);
}

static void subStrings(const char* a, const char* b, char* result) {
	static char A[BUF], B[BUF], OUT[BUF];
	strncpy(A, a, BUF - 1); A[BUF - 1] = '\0';
	strncpy(B, b, BUF - 1); B[BUF - 1] = '\0';

	static char intA[BUF], intB[BUF], fracA[BUF], fracB[BUF];
	fracA[0] = fracB[0] = 0;
	const char* dotA = strchr(A, '.');
	const char* dotB = strchr(B, '.');
	if (dotA) { int la = dotA - A; if (la >= BUF) { strcpy(result, "NaN"); return; } strncpy(intA, A, la); intA[la] = 0; strncpy(fracA, dotA + 1, BUF - 1); }
	else strncpy(intA, A, BUF - 1);
	if (dotB) { int lb = dotB - B; if (lb >= BUF) { strcpy(result, "NaN"); return; } strncpy(intB, B, lb); intB[lb] = 0; strncpy(fracB, dotB + 1, BUF - 1); }
	else strncpy(intB, B, BUF - 1);
	trim_str(intA); trim_str(intB); trim_str(fracA); trim_str(fracB);
	int la_frac = strlen(fracA), lb_frac = strlen(fracB);
	int fracLen = la_frac > lb_frac ? la_frac : lb_frac;
	if (fracLen >= BUF / 2) { strcpy(result, "NaN"); return; }
	while ((int)strlen(fracA) < fracLen) strcat(fracA, "0");
	while ((int)strlen(fracB) < fracLen) strcat(fracB, "0");
	static char fullA[BUF], fullB[BUF];
	snprintf(fullA, sizeof(fullA), "%s%s", intA, fracA);
	snprintf(fullB, sizeof(fullB), "%s%s", intB, fracB);
	trim_str(fullA); trim_str(fullB);
	int swapped = 0;
	if (cmp_intstr(fullA, fullB) < 0) {
		char tmp[BUF];
		strcpy(tmp, fullA); strcpy(fullA, fullB); strcpy(fullB, tmp);
		swapped = 1;
	}
	int i = strlen(fullA) - 1, j = strlen(fullB) - 1;
	static char rev[BUF];
	int p = 0, borrow = 0;
	while (i >= 0 || j >= 0) {
		int da = (i >= 0 ? fullA[i] - '0' : 0);
		int db = (j >= 0 ? fullB[j] - '0' : 0);
		int d = da - db - borrow;
		if (d < 0) { d += 10; borrow = 1; }
		else borrow = 0;
		rev[p++] = '0' + d;
		i--; j--;
	}
	while (p > 1 && rev[p - 1] == '0') p--;
	int k;
	for (k = 0; k < p; k++) OUT[k] = rev[p - 1 - k];
	OUT[k] = '\0';
	if (fracLen > 0) {
		int len = strlen(OUT);
		if (len <= fracLen) {
			int need = fracLen + 1 - len;
			memmove(OUT + need, OUT, len + 1);
			for (int z = 0; z < need; ++z) OUT[z] = '0';
			len = strlen(OUT);
		}
		memmove(OUT + (len - fracLen) + 1, OUT + (len - fracLen), fracLen + 1);
		OUT[len - fracLen] = '.';
	}
	trim_str(OUT);
	if (strcmp(OUT, "0") == 0) swapped = 0;
	if (swapped) {
		if (strlen(OUT) + 2 >= BUF) { strcpy(result, "NaN"); return; }
		memmove(result + 1, OUT, strlen(OUT) + 1);
		result[0] = '-';
	}
	else strcpy(result, OUT);
}

static void mulStrings(const char* a, const char* b, char* result) {
	if (!a || !b) { strcpy(result, "NaN"); return; }
	int neg = 0;
	if (a[0] == '-') { neg = !neg; a++; }
	if (b[0] == '-') { neg = !neg; b++; }
	int decA = 0, decB = 0;
	static char na[BUF], nb[BUF];
	int j = 0;
	for (int i = 0; a[i]; i++) {
		if (a[i] == '.') decA = strlen(a) - i - 1;
		else na[j++] = a[i];
	}
	na[j] = '\0';
	j = 0;
	for (int i = 0; b[i]; i++) {
		if (b[i] == '.') decB = strlen(b) - i - 1;
		else nb[j++] = b[i];
	}
	nb[j] = '\0';
	int la = strlen(na), lb = strlen(nb);
	if (la == 0 || lb == 0) { strcpy(result, "0"); return; }
	static int prod[BUF];
	for (int i = 0; i < BUF; ++i) prod[i] = 0;
	for (int i = la - 1; i >= 0; --i) {
		if (na[i] < '0' || na[i] > '9') continue;
		for (int j = lb - 1; j >= 0; --j) {
			if (nb[j] < '0' || nb[j] > '9') continue;
			prod[i + j + 1] += (na[i] - '0') * (nb[j] - '0');
		}
	}

	int n = la + lb;
	for (int i = n - 1; i > 0; --i) {
		if (prod[i] >= 10) {
			prod[i - 1] += prod[i] / 10;
			prod[i] %= 10;
		}
	}
	int start = 0;
	while (start < n && prod[start] == 0) start++;
	if (start == n) { strcpy(result, "0"); return; }

	static char temp[BUF];
	int pos = 0;
	for (int i = start; i < n; ++i)
		temp[pos++] = '0' + prod[i];
	temp[pos] = '\0';
	int totalDec = decA + decB;
	if (totalDec > 0) {
		int len = strlen(temp);
		if (totalDec >= len) {
			char shifted[BUF] = "0.";
			for (int i = 0; i < totalDec - len; i++) strcat(shifted, "0");
			strcat(shifted, temp);
			strcpy(temp, shifted);
		}
		else {
			memmove(temp + (len - totalDec + 1), temp + (len - totalDec), totalDec + 1);
			temp[len - totalDec] = '.';
		}
	}
	trim_str(temp);
	reduceDecimals(temp, MAX_PREC);
	if (neg && strcmp(temp, "0") != 0) {
		char signedRes[BUF] = "-";
		strcat(signedRes, temp);
		strcpy(result, signedRes);
	}
	else {
		strcpy(result, temp);
	}
}

static void divEuclidStrings(const char* a, const char* b, char* q, char* r) {
	if (b == NULL || strcmp(b, "0") == 0) { strcpy(q, "NaN"); strcpy(r, "NaN"); return; }
	int la = strlen(a);
	static char current[BUF]; current[0] = '\0';
	static char tmp[BUF];
	int qpos = 0;
	for (int i = 0; i < la; ++i) {
		int len = strlen(current);
		if (len + 1 < BUF) { current[len] = a[i]; current[len + 1] = '\0'; }
		trim_str(current);
		int count = 0;
		while (compareStrings(current, b) >= 0) {
			subStrings(current, b, tmp);
			strcpy(current, tmp);
			trim_str(current);
			++count;
		}
		if (qpos + 1 < BUF) q[qpos++] = '0' + count;
	}
	if (qpos == 0) { strcpy(q, "0"); }
	else { q[qpos] = '\0'; trim_str(q); }
	if (strlen(current) == 0) strcpy(r, "0"); else strcpy(r, current);
}

static void divStrings(const char* a, const char* b, char* result, int precision) {
	if (b == NULL || strcmp(b, "0") == 0) { strcpy(result, "NaN"); return; }
	if (precision < 0) precision = 0;
	if (precision > MAX_PREC) precision = MAX_PREC;

	static char na[BUF], nb[BUF];
	int decA = 0, decB = 0;
	int j = 0;
	for (int i = 0; a[i]; i++) {
		if (a[i] == '.') decA = strlen(a) - i - 1;
		else na[j++] = a[i];
	}
	na[j] = '\0';

	j = 0;
	for (int i = 0; b[i]; i++) {
		if (b[i] == '.') decB = strlen(b) - i - 1;
		else nb[j++] = b[i];
	}
	nb[j] = '\0';

	int shift = decB - decA;
	if (shift > 0) {
		int len = strlen(na);
		for (int i = 0; i < shift; i++) na[len + i] = '0';
		na[len + shift] = '\0';
	}
	else if (shift < 0) {
		int len = strlen(nb);
		for (int i = 0; i < -shift; i++) nb[len + i] = '0';
		nb[len - shift] = '\0';
	}

	static char q[BUF], r[BUF], tmp[BUF];
	divEuclidStrings(na, nb, q, r);

	if (precision == 0) {
		strcpy(result, q);
		return;
	}

	static char res[BUF];
	snprintf(res, sizeof(res), "%s.", q);
	static char rem[BUF];
	strcpy(rem, r);

	for (int i = 0; i < precision; i++) {
		int rl = strlen(rem);
		if (rl + 1 < BUF) {
			rem[rl] = '0';
			rem[rl + 1] = '\0';
		}
		divEuclidStrings(rem, nb, tmp, rem);
		strncat(res, tmp, 1);
		if (strcmp(rem, "0") == 0) break;
	}

	strncpy(result, res, BUF - 1);
	result[BUF - 1] = '\0';

	trim_str(result);
}

static void powerStrings(const char* base, const char* exponent, char* result)
{
	if (strchr(exponent, '.')) {
		static char lnBase[BUF], temp[BUF];
		lnStrings(base, lnBase);
		if (!strcmp(lnBase, "NaN"))
		{
			strcpy(result, lnBase);
			return;
		}
		mulStrings(lnBase, exponent, temp);
		expStrings(temp, result);
		return;
	}

	int exp = atoi(exponent);
	if (exp == 0) { strcpy(result, "1"); return; }
	if (exp == 1) { strcpy(result, base); return; }

	static char baseInt[BUF];
	strcpy(baseInt, base);
	int decDigits = 0;

	char* dot = strchr(baseInt, '.');
	if (dot) {
		decDigits = strlen(dot + 1);
		memmove(dot, dot + 1, strlen(dot));
	}

	static char temp[BUF];
	strcpy(temp, "1");
	for (int i = 0; i < exp; i++) {
		char prod[BUF];
		mulStrings(temp, baseInt, prod);
		strcpy(temp, prod);
	}

	if (decDigits > 0) {
		int totalDec = decDigits * exp;
		int len = strlen(temp);
		if (len <= totalDec) {
			memmove(temp + (totalDec - len) + 2, temp, len + 1);
			memset(temp, '0', totalDec - len + 2);
			temp[1] = '.';
		}
		else {
			memmove(temp + len - totalDec + 1, temp + len - totalDec, totalDec + 1);
			temp[len - totalDec] = '.';
		}
	}

	strcpy(result, temp);
	trim_str(result);
}

static void gcdStrings(const char* a, const char* b, char* result) {
	static char A[BUF], B[BUF], q[BUF], r[BUF];
	strncpy(A, a, BUF - 1); A[BUF - 1] = '\0';
	strncpy(B, b, BUF - 1); B[BUF - 1] = '\0';

	char* dotA = strchr(A, '.');
	if (dotA) *dotA = '\0';
	char* dotB = strchr(B, '.');
	if (dotB) *dotB = '\0';

	while (strcmp(B, "0") != 0) {
		divEuclidStrings(A, B, q, r);
		strncpy(A, B, BUF - 1);
		strncpy(B, r, BUF - 1);
	}

	strncpy(result, A, BUF - 1);
	result[BUF - 1] = '\0';
	trim_str(result);
}

void factorialString(int n, char* result) {
	if (n < 0) {
		strcpy(result, "NaN");
		return;
	}
	strcpy(result, "1");
	static char tmp[BUF], mult[24];
	for (int i = 2; i <= n; ++i) {
		snprintf(mult, sizeof(mult), "%d", i);
		mulStrings(result, mult, tmp);
		if ((int)strlen(tmp) >= BUF - 2) {
			strcpy(result, "NaN");
			return;
		}
		strcpy(result, tmp);
	}
}

static int cmpStrings(const char* a_in, const char* b_in) {
	while (*a_in == ' ' || *a_in == '\t') a_in++;
	while (*b_in == ' ' || *b_in == '\t') b_in++;
	if (*b_in == '-') return 1;
	const char* a = a_in, * b = b_in;
	while (*a == '0' && a[1] && a[1] != '.') a++;
	while (*b == '0' && b[1] && b[1] != '.') b++;
	const char* pa = strchr(a, '.');
	const char* pb = strchr(b, '.');
	int lena = pa ? (int)(pa - a) : (int)strlen(a);
	int lenb = pb ? (int)(pb - b) : (int)strlen(b);
	if (lena != lenb) return (lena > lenb) ? 1 : -1;
	int cmp = strncmp(a, b, lena);
	if (cmp < 0) return -1;
	if (cmp > 0) return 1;
	const char* fa = pa ? pa + 1 : "";
	const char* fb = pb ? pb + 1 : "";
	while (*fa || *fb) {
		char ca = *fa ? *fa++ : '0';
		char cb = *fb ? *fb++ : '0';
		if (ca < cb) return -1;
		if (ca > cb) return 1;
	}
	return 0;
}

static const char* invOdd[] = {
	"1",               // 1/1
	"0.3333333333",    // 1/3
	"0.2",             // 1/5
	"0.1428571428",    // 1/7
	"0.1111111111",    // 1/9
	"0.0909090909",    // 1/11
	"0.0769230769",    // 1/13
	"0.0666666666",    // 1/15
	"0.0588235294",    // 1/17
	"0.0526315789",    // 1/19
	"0.0476190476"     // 1/21
};
#define LN_ITER 11
static const char* LN2 = "0.6931471805599453";

static void lnStrings(const char* x_in, char* result)
{
	static char x[BUF], y[BUF], yp2[BUF], term[BUF], sum[BUF], tmp[BUF], kln2[BUF];
	if (!strcmp(x_in, "0") || x_in[0] == '-') { strcpy(result, "NaN"); return; }
	if (!strcmp(x_in, "1")) { strcpy(result, "0"); return; }
	// si x < 1 : ln(x)= -ln(1/x)
	if (x_in[0] == '0' && x_in[1] == '.') {
		divStrings("1", x_in, tmp, MAX_PREC);
		lnStrings(tmp, result);
		if (result[0] == '-') strcpy(result, result + 1);
		else { tmp[0] = '-'; strcpy(tmp + 1, result); strcpy(result, tmp); }
		return;
	}
	strncpy(x, x_in, BUF - 1); x[BUF - 1] = 0;
	int k = 0;
	while (cmpStrings(x, "2") > 0) {
		divStrings(x, "2", x, MAX_PREC);
		k++;
	}
	// y = (x-1)/(x+1)
	subStrings(x, "1", tmp);        // tmp = x-1
	addStrings(x, "1", y);          // y = x+1
	divStrings(tmp, y, y, MAX_PREC); // y = (x-1)/(x+1)
	strcpy(sum, y);
	strcpy(term, y);
	mulStrings(y, y, yp2);
	for (int i = 1; i < LN_ITER; i++) {
		mulStrings(term, yp2, term);     // term *= y²
		mulStrings(term, invOdd[i], tmp); // tmp = term/(2i+1)
		addStrings(sum, tmp, sum);
	}
	mulStrings(sum, "2", sum);
	if (k > 0) {
		char kstr[16];
		snprintf(kstr, sizeof(kstr), "%d", k);
		mulStrings(LN2, kstr, kln2);
		addStrings(sum, kln2, sum);
	}
	strncpy(result, sum, BUF - 1); result[BUF - 1] = 0;
	trim_str(result);
}

static const char* invFact[] = {
	"1",
	"1",
	"0.5",
	"0.166666666666667",
	"0.041666666666667",
	"0.008333333333333",
	"0.001388888888889",
	"0.000198412698413",
	"0.000024801587302",
	"0.000002755731922",
	"0.000000275573192",
	"0.000000025052108",
	"0.000000002087676",
	"0.000000000160590",
	"0.000000000011471",
	"0.000000000000765"
};
#define EXP_ITER 16

static void expStrings(const char* xin, char* result)
{
	if (xin[0] == '-') {
		static char absx[BUF], exppos[BUF];
		strcpy(absx, xin + 1);
		expStrings(absx, exppos);
		divStrings("1", exppos, result, MAX_PREC);
		return;
	}
	static char x[BUF], t[BUF], term[BUF], sum[BUF], tmp[BUF];
	strncpy(x, xin, BUF - 1); x[BUF - 1] = 0;
	if (!strcmp(x, "0")) { strcpy(result, "1"); return; }
	int k = 0;
	snprintf(tmp, sizeof(tmp), "1");
	while (cmpStrings(x, "1") > 0) {
		divStrings(x, "2", x, MAX_PREC);
		k++;
	}
	strncpy(t, x, BUF - 1);
	strcpy(sum, "1");
	strcpy(term, "1");
	for (int i = 1; i < EXP_ITER; i++) {
		mulStrings(term, t, term);       // term *= t
		mulStrings(term, invFact[i], tmp);
		addStrings(sum, tmp, sum);
	}
	while (k-- > 0) {
		mulStrings(sum, sum, sum);
	}
	strncpy(result, sum, BUF - 1); result[BUF - 1] = 0;
	trim_str(result);
}

Number sub(Number left, Number right)
{
	if (!strcmp(left.nombre, right.nombre))
		return (Number) { 1, strdup("0") };
	if (compareStrings(right.nombre, left.nombre) > 0)
	{
		Number resultat = sub(right, left);
		resultat.signe *= -1;
		return resultat;
	}
	static char res[BUF];
	subStrings(left.nombre, right.nombre, res);
	return create(1, res);
}

Number add(Number left, Number right)
{
	static char res[BUF];
	addStrings(left.nombre, right.nombre, res);
	return create(1, res);
}

Number prod(Number left, Number right)
{
	static char res[BUF];
	mulStrings(left.nombre, right.nombre, res);
	return create(1, res);
}

Number int_divid(Number num, Number denom, Number* rem)
{
	static char res[BUF], quot[BUF];
	divEuclidStrings(num.nombre, denom.nombre, quot, res);
	if (!strcmp(res, "NaN"))
	{
		(*rem).nombre = strdup("UNDEF");
		return create(1, "UNDEF");
	}
	if (rem != NULL)
		(*rem).nombre = strdup(res);
	return create(1, quot);
}

Number divid(Number num, Number denom)
{
	static char res[BUF];
	divStrings(num.nombre, denom.nombre, res, 15);
	if (!strcmp(res, "NaN"))
		return create(1, "UNDEF");
	return create(1, res);
}

Number gcd(Number num, Number denom)
{
	static char res[BUF];
	gcdStrings(num.nombre, denom.nombre, res);
	return create(1, res);
}

Number Exponentiel(Number x)
{
	static char res[BUF];
	expStrings(x.nombre, res);
	if (x.signe == -1)
	{
		divStrings("1", res, res, MAX_PREC);
	}
	return create(1, res);
}

Number Logarithme(Number x)
{
	static char res[BUF];
	int sign = 1;
	lnStrings(x.nombre, res);
	if (!strcmp(res, "NaN"))
		return create(1, "UNDEF");
	if (res[0] == '-') {
		memmove(res, res + 1, strlen(res));
		sign = -1;
	}
	return create(sign, res);
}

Number ExponentiationRapide(Number bas, Number exposant)
{
	static char res[BUF];
	powerStrings(bas.nombre, exposant.nombre, res);
	if (!strcmp(res, "NaN"))
		return create(1, "UNDEF");
	return create(1, res);
}

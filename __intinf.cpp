#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <vector>
using namespace std;

class __intinf {
#define BASE 1000000000

   public:
    typedef long long value;
    void __new(size_t len) {
        if (a != NULL) delete[] a;
        a = new value[len];
        len = 1;
        a[0] = 0;
        sgn = 1;
    }

    __intinf() : a(NULL), base(BASE) { __new(1); }
    __intinf(value x) : a(NULL), base(BASE) {
        __new(1);
        *this = x;
    }
    __intinf(value x, value _base) : a(NULL), base(_base) {
        __new(1);
        *this = x;
    }
    __intinf(const __intinf &B) : a(NULL), base(BASE) {
        __new(1);
        *this = B;
    }
    ~__intinf() { delete[] a; }

    __intinf &operator=(value x) {
        size_t _len = 1;
        for (value x1 = max(x, -x); x1 >= base; ++_len, x1 /= base)
            ;
        __new(_len);
        if (x < 0)
            x = -x, sgn = 0;
        else
            sgn = 1;
        len = 0;
        for (; x; x /= base) a[len++] = x % base;
        if (!len) a[len++] = 0;
        return *this;
    }
    __intinf &operator=(const __intinf &A) {
        __new(A.len);
        len = A.len;
        memcpy(a, A.a, sizeof(value) * len);
        base = A.base;
        sgn = A.sgn;
        return *this;
    }

    friend __intinf operator-(__intinf A) {
        A.sgn = 1 - A.sgn;
        return A;
    }
    bool operator!() { return (len == 1 && a[0] == 0) ? 1 : 0; }

    friend __intinf operator+(__intinf A, __intinf B) {
        if (A.sgn != B.sgn) {
            B.sgn = 1 - B.sgn;
            return A - B;
        }
        if (A.base != B.base) {
            if (A.base > B.base)
                B.set_base(A.base);
            else
                A.set_base(B.base);
        }
        __intinf ret;
        ret.set_base(A.base);
        int len = max(A.len, B.len);
        ret.__new(len + 1);
        ret.sgn = A.sgn;
        memset(ret.a, 0, sizeof(value) * (len + 1));
        for (int i = 0; i < len; ++i) {
            if (i < A.len) ret.a[i] += A.a[i];
            if (i < B.len) ret.a[i] += B.a[i];
        }
        for (int i = 0; i < len; ++i)
            if (ret.a[i] >= ret.base) ++ret.a[i + 1], ret.a[i] -= ret.base;
        if (ret.a[len])
            ret.len = len + 1;
        else
            ret.len = len;
        if (!ret) ret.sgn = 1;
        return ret;
    }

    friend __intinf operator-(__intinf A, __intinf B) {
        if (A.sgn != B.sgn) {
            B.sgn = 1 - B.sgn;
            return A + B;
        }
        if (A.base != B.base) {
            if (A.base > B.base)
                B.set_base(A.base);
            else
                A.set_base(B.base);
        }
        if (small(A, B)) {
            __intinf t = A;
            A = B;
            B = t;
            A.sgn = 1 - A.sgn;
        }
        __intinf ret;
        ret.set_base(A.base);
        int len = max(A.len, B.len);
        ret.__new(len);
        ret.sgn = A.sgn;
        memset(ret.a, 0, sizeof(value) * len);
        for (int i = 0; i < len; ++i) {
            if (i >= B.len)
                ret.a[i] += A.a[i];
            else
                ret.a[i] += A.a[i] - B.a[i];
            if (ret.a[i] < 0) ret.a[i] += ret.base, --ret.a[i + 1];
        }
        while (len > 1 && !ret.a[len - 1]) --len;
        ret.len = len;
        if (!ret) ret.sgn = 1;
        return ret;
    }

    friend __intinf operator*(__intinf A, __intinf B) {
        if (A.base != B.base) {
            if (A.base > B.base)
                B.set_base(A.base);
            else
                A.set_base(B.base);
        }
        __intinf ret;
        ret.set_base(A.base);
        int len = A.len + B.len;
        ret.__new(len);
        ret.sgn = (A.sgn == B.sgn);
        memset(ret.a, 0, sizeof(value) * len);
        for (int i = 0; i < A.len; ++i)
            for (int j = 0; j < B.len; ++j) {
                ret.a[i + j] += A.a[i] * B.a[j];
                ret.a[i + j + 1] += ret.a[i + j] / ret.base;
                ret.a[i + j] %= ret.base;
            }
        while (len > 1 && !ret.a[len - 1]) --len;
        ret.len = len;
        return ret;
    }

    friend pair<__intinf, __intinf> div(__intinf A, __intinf B) {
        assert(B != 0);
        if (A.base != B.base) {
            if (A.base > B.base)
                B.set_base(A.base);
            else
                A.set_base(B.base);
        }
        if (A < B) return make_pair(__intinf(0), A);
        __intinf C, D;
        C.set_base(A.base);
        D.set_base(A.base);
        C.__new(A.len);
        C.len = A.len;
        D.__new(A.len);
        D.len = A.len;
        memset(D.a, 0, sizeof(value) * A.len);
        bool C_sgn = (A.sgn == B.sgn), D_sgn = A.sgn;
        A.sgn = B.sgn = 1;
        for (int i = A.len - 1; i >= 0; --i) {
            C.a[i] = 0;
            D = D * D.base;
            D.a[0] = A.a[i];
            int l = 0, r = A.base - 1, mid;
            while (r >= l) {
                mid = (l + r) >> 1;
                if (B * mid < D + 1)
                    l = mid + 1;
                else
                    r = mid - 1;
            }
            C.a[i] = r;
            D = D - B * r;
        }
        C.sgn = C_sgn;
        D.sgn = D_sgn;
        if (!D) D.sgn = 1;
        while (C.len > 1 && !C.a[C.len - 1]) --C.len;
        return make_pair(C, D);
    }

    __intinf operator/(value x) {
        assert(x != 0);
        value d = 0;
        __intinf ret;
        ret.set_base(base);
        ret.__new(len);
        ret.len = len;
        if (x < 0)
            x = -x, ret.sgn = (sgn == 0);
        else
            ret.sgn = (sgn == 1);
        for (int i = len - 1; i >= 0; --i)
            d = d * base + a[i], ret.a[i] = d / x, d %= x;
        while (ret.len > 1 && !ret.a[ret.len - 1]) --ret.len;
        return ret;
    }

    __intinf operator%(value x) {
        value d = 0;
        if (x < 0) x = -x;
        for (int i = len - 1; i >= 0; --i) d = (d * base + a[i]) % x;
        return d;
    }

    friend __intinf abs(__intinf A) {
        A.sgn = 1;
        return A;
    }
    friend bool small(__intinf A, __intinf B) {
        if (A.base != B.base) {
            if (A.base > B.base)
                B.set_base(A.base);
            else
                A.set_base(B.base);
        }
        if (A.len != B.len) return A.len < B.len;
        for (int i = A.len - 1; i >= 0; --i)
            if (A.a[i] != B.a[i]) return A.a[i] < B.a[i];
        return 0;
    }

    friend bool operator<(__intinf A, __intinf B) {
        if (A.sgn != B.sgn) return A.sgn < B.sgn;
        return A.sgn == 1 ? small(A, B) : small(B, A);
    }

    friend bool operator==(__intinf A, __intinf B) {
        if (A.base != B.base) {
            if (A.base > B.base)
                B.set_base(A.base);
            else
                A.set_base(B.base);
        }
        if (A.sgn != B.sgn || A.len != B.len) return 0;
        for (int i = 0; i < A.len; ++i)
            if (A.a[i] != B.a[i]) return 0;
        return 1;
    }

    friend bool operator!=(__intinf A, __intinf B) { return !(A == B); }
    friend bool operator>(__intinf A, __intinf B) { return !(A < B || A == B); }
    friend bool operator<=(__intinf A, __intinf B) { return A < B || A == B; }
    friend bool operator>=(__intinf A, __intinf B) { return A > B || A == B; }
    __intinf operator/(__intinf B) { return div(*this, B).first; }
    __intinf operator%(__intinf B) { return div(*this, B).second; }
    __intinf &operator+=(__intinf B) {
        *this = *this + B;
        return *this;
    }
    __intinf &operator-=(__intinf B) {
        *this = *this - B;
        return *this;
    }
    __intinf &operator*=(__intinf B) {
        *this = *this * B;
        return *this;
    }
    __intinf &operator/=(__intinf B) {
        *this = *this / B;
        return *this;
    }
    __intinf &operator%=(__intinf B) {
        *this = *this % B;
        return *this;
    }
    __intinf &operator++() {
        *this = *this + 1;
        return *this;
    }
    __intinf &operator--() {
        *this = *this - 1;
        return *this;
    }
    __intinf operator++(int) {
        __intinf ret(*this);
        *this = *this + 1;
        return ret;
    }
    __intinf operator--(int) {
        __intinf ret(*this);
        *this = *this - 1;
        return ret;
    }
    __intinf operator+(value x) { return *this + __intinf(x, this->base); }
    __intinf operator-(value x) { return *this - __intinf(x, this->base); }
    __intinf operator*(value x) { return *this * __intinf(x, this->base); }
    __intinf operator+=(value x) {
        *this = *this + x;
        return *this;
    }
    __intinf operator-=(value x) {
        *this = *this - x;
        return *this;
    }
    __intinf operator*=(value x) {
        *this = *this * x;
        return *this;
    }
    __intinf operator/=(value x) {
        *this = *this / x;
        return *this;
    }
    __intinf operator%=(value x) {
        *this = *this % x;
        return *this;
    }
    bool operator<(value x) { return *this < __intinf(x, this->base); }
    bool operator>(value x) { return *this > __intinf(x, this->base); }
    bool operator==(value x) { return *this == __intinf(x, this->base); }
    bool operator!=(value x) { return *this != __intinf(x, this->base); }
    bool operator<=(value x) { return *this <= __intinf(x, this->base); }
    bool operator>=(value x) { return *this >= __intinf(x, this->base); }

    friend __intinf gcd(__intinf a, __intinf b) {
        __intinf t;
        int acc = 0;
        while (a % 2 == 0 && b % 2 == 0) a /= 2, b /= 2, ++acc;
        while (a % 2 == 0) a /= 2;
        while (b % 2 == 0) b /= 2;
        if (a < b) t = a, a = b, b = t;
        while (a != b) {
            a -= b;
            if (a < b) t = a, a = b, b = t;
        }
        for (int i = 1; i <= acc; ++i) a *= 2;
        return a;
    }

    friend __intinf pow(__intinf a, __intinf b) {
        __intinf ret = 1;
        for (; b > 0; b /= 2) {
            if (b % 2 == 1) ret *= a;
            a *= a;
        }
        return ret;
    }

    friend __intinf sqrt(__intinf a) {
        assert(a >= 0);
        __intinf l = 0, r = a, mid;
        while (r >= l) {
            mid = (l + r) / 2;
            if (mid * mid <= a) l = mid + 1;
            else r = mid - 1;
        }
        return r;
    }

    void put(char *c) {
        char *t = c;
        for (int i = 0; i < len - 1; ++i)
            for (value x = a[i], b = base / 10; b; b /= 10)
                *t++ = x % 10 + '0', x /= 10;
        for (value x = a[len - 1]; x > 0; x /= 10) *t++ = x % 10 + '0';
        if (len == 1 && a[len] == 0) *t++ = '0';
        if (sgn == 0) *t++ = '-';
        *t = 0;
        reverse(c, t);
    }

    void get(char *c) {
        size_t base_L = get_baseL(), b = 1;
        int c_len = strlen(c);
        value x = 0;
        __new((c_len + base_L - 1) / base_L);
        len = 0;
        if (*c == '-')
            sgn = 0, ++c, --c_len;
        else
            sgn = 1;
        for (; --c_len >= 0;) {
            x += (c[c_len] - '0') * b;
            b *= 10;
            if (b == base) a[len++] = x, x = 0, b = 1;
        }
        if (!len || x) a[len++] = x;
        while (len > 1 && !a[len - 1]) --len;
    }

    void set_base(int _base) {
        if (base == _base) return;
        char *c = new char[len * get_baseL() + 1];
        put(c);
        base = _base;
        get(c);
        delete[] c;
    }

    void set_baseL(int _l) {
        size_t _base = 1;
        for (; --_l;) _base *= 10;
        set_base(_base);
    }

    void read() {
        vector<char> s;
        // s.clear();
        char ch;
        scanf(" %c", &ch);
        if (ch == '-') s.push_back('-'), ch = getchar();
        for (; ch >= '0' && ch <= '9'; ch = getchar()) s.push_back(ch);
        char *c = new char[s.size() + 1];
        for (int i = 0; i < s.size(); ++i) c[i] = s[i];
        c[s.size()] = 0;
        get(c);
        delete[] c;
        if (!*this) this->sgn = 1;
    }

    void print() {
        if (sgn == 0) putchar('-');
        printf("%d", (int)a[len - 1]);
        for (int i = len - 2; i >= 0; --i) {
            for (int j = base / 10; j >= 10; j /= 10)
                if (a[i] < j)
                    putchar('0');
                else
                    break;
            printf("%d", (int)a[i]);
        }
    }

    void println() {
        print();
        putchar('\n');
    }

   private:
    value *a, base;
    int len;
    bool sgn;
    size_t get_baseL() const {
        size_t ret = 0;
        for (int b = base / 10; b; b /= 10, ++ret)
            ;
        return ret;
    }

#undef BASE
};

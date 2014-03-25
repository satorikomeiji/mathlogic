#include <iostream>
#include <vector>
#include <cmath>
#include <cstdio>
typedef long long ll;
struct Z
{
    static const ll args_size = 1;

    static ll eval(std::vector < ll > a)
    {
        return 0;
    }
};

struct N
{
    static const ll args_size = 1;

    static ll eval(std::vector < ll > a)
    {
        return a[0] + 1;
    }
};

template < ll n, ll k >
struct U
{
    static const ll args_size = n;

    static ll eval(std::vector < ll > a)
    {
        return a[k - 1];
    }
};

template < class F, class g, class ... G >
struct S
{
    static const ll args_size = g::args_size;

    static ll eval(std::vector < ll > a)
    {
        return F::eval((std::vector < ll >) {g::eval(a), G::eval(a) ...});
    }
};

template <class F, class G>
struct R
{
    static const ll args_size = F::args_size + 1;

    static ll eval(std::vector < ll > a)
    {
        std::vector < ll > tmp(a.begin(), a.end() - 1);
        if (a.back())
        {
            tmp.push_back(a.back() - 1);
            tmp.push_back(R<F, G>::eval(tmp));
            return G::eval(tmp);
        }
        return F::eval(tmp);
    }
};

template <class F>
struct M
{
    static const ll args_size = F::args_size - 1;

    static ll eval(std::vector < ll > a)
    {
        std::vector < ll > tmp = a;
        tmp.push_back(0);
        for (ll y = 0; F::eval(tmp); y++)
        {
            tmp[args_size] = y;
        }
        return tmp[args_size];
    }
};

template<class G, class... K>
ll apply(K... x)
{
    std::vector<ll> a = { x... };
    return G::eval(a);
}

struct native_plus 
{
    static ll eval(std::vector < ll > a)
    {
        return a[0] + a[1];
    }
};

struct native_minus
{
    static ll eval(std::vector <ll> a)
    {
        if (a[0] >= a[1])
            return a[0] - a[1];
        return 0;
    }
};

struct native_mul
{
    static ll eval(std::vector < ll > a)
    {
        return a[0] * a[1];
    }
};

struct native_pow
{
    static ll eval(std::vector < ll > a)
    {
        return (ll)pow((double)a[0], (double)a[1]);
    }
};

struct native_div
{
    static ll eval(std::vector < ll > a)
    {
        return a[0] / a[1];
    }
};

struct native_mod
{
    static ll eval(std::vector < ll > a)
    {
        return a[0] % a[1];
    }
};



struct native_equals
{
    static ll eval(std::vector <ll> a)
    {
        if (a[0] == a[1])
            return 1;
        else
            return 0;
    }
};

typedef S<N, Z> r_one;
typedef S<N, r_one> r_two;
typedef S< R< Z, U< 3, 2 > >, U< 1, 1 >, U< 1, 1 > > r_dec;
typedef S< native_plus, U<2, 1>, U<2, 2> > r_plus;
typedef S< native_minus, U<2, 1>, U<2, 2> > r_minus;
typedef S< native_mul, U<2, 1>, U<2, 2> > r_mul ;
typedef S< native_pow, U<2, 1>, U<2, 2> > r_pow;
typedef S< native_div, U<2, 1>, U<2, 2> > r_div;
typedef S< native_mod, U<2, 1>, U<2, 2> > r_mod;
typedef S < R< N, S< Z, U< 3, 3 > > >, U< 1, 1 >, U< 1, 1 > > NOT;
typedef S< S< NOT, NOT >, r_minus > r_greater;
typedef S < S< NOT, NOT >, S< r_minus, U< 2, 2 >, U< 2, 1 > > > r_less;
typedef S< native_equals, U<2, 1>, U<2, 2> > r_equals;
typedef S< r_minus, S< r_plus, U< 3, 3 >, S< r_mul , S< S < NOT, NOT >, U < 3, 1> >, U < 3, 2 > > >, S< r_mul , S < S< NOT, NOT >, U< 3, 1> >, U< 3, 3 > > > IF;
typedef S< r_dec, M< S< S< r_equals, r_mod, Z > , U< 3, 2 >, S< r_pow, U< 3, 1 >, U< 3, 3> > > > > plog;
typedef S< R< S< r_greater, U< 1, 1 >, r_one >, S< S< S< S< NOT, NOT >, r_mul > , S< r_mod, U< 3, 1 >, U< 3, 2 > >, U< 3, 3 > >, U< 3, 1 >, S< S< N, N >, U< 3, 2 > >, U< 3, 3 > > >, U< 1, 1 >,
            S< r_dec, S< r_div, U< 1, 1 >, r_two > > > isPrime;
typedef S< R< Z, S< r_plus, S< isPrime, U< 3, 2 > >, U< 3, 3 > > >, U< 1, 1 >, S< N, U< 1, 1 > > > primeBefore;
typedef S< M< S< r_greater, U< 2, 1 >, S< primeBefore, U< 2, 2 > > > >, N > nthPrime;
typedef S< r_dec, S< plog, r_two , U< 1, 1 > > > size;
typedef S< r_mul , S< r_two , U<2, 1> > , S< r_mul , U< 2, 1 >,
            S< r_pow, S< nthPrime, S< N, S< size, U< 2, 1 > > > >, S< N, U< 2, 2 > > > > > push;
typedef S< push, S< push, U<3, 1>, U<3, 2> >, U<3, 3> > push2;
typedef S< r_dec, S< plog, S< nthPrime, size >, U< 1, 1 > > > top;
typedef S< r_dec, S< plog, S< nthPrime, S< r_dec, size > >, U< 1, 1 > > > top2;
typedef S< r_div, S< r_div, U< 1, 1 >, S< r_pow, S< nthPrime, size >, S< N, top > > >, r_two > pop;
typedef S< pop, S< pop, U<1, 1> > > pop2;
//n==0
typedef S< push, pop2, S< N, top> > case1;
//m==0
typedef S< push2, pop2, S< r_dec, top2 >, S < N, Z > > case2;
//m>0
typedef S< S< push, S< push, S< push, U<4, 1>, U<4, 2> >, U<4, 3> >, U<4, 4> > , pop2, S< r_dec, top2 >, top2, S< r_dec, top> > case3;
typedef S< IF, S< r_equals, top, Z >, case2, case3> step;
typedef R< S< push2, S< N, S < N, Z > > , U<2, 1>, U<2, 2> >, S< S< IF, S< r_equals, top2, Z >, case1, step >, U<4,4> > > steps;
typedef M< S< r_minus, S< S< size, S< steps, U<3, 1>, U<3, 2>, U<3, 3> > >, U<3, 1>, U<3, 2>, U<3, 3> >, S < N, Z > > > sc;
typedef S< top, S< steps, U<3,1>, U<3,2>, S< sc, U<3, 1>, U<3, 2> > > > ackerman;



int main () {
    int n, m;
    std::cout << "Enter n,m" << std::endl;
    std::cin >> n >> m;
    std::cout << "Ackerman(" << n << "," << m << ") = " << (apply<ackerman>(n,m)) << std::endl;
}

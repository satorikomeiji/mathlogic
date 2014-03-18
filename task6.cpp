#include <iostream>
#include <vector>


using namespace std;
typedef unsigned int natural;


typedef std::vector<natural> arguments;


struct Z {
static natural eval(const arguments args) {
        return 0;
    }
    template<typename... T>
    static natural apply(T... x) {
        arguments args{ x... };
        return eval(args);
    }
};
struct N {
    static natural eval(const arguments  args) {
        return args[0] + 1;
    }
    template<typename... T>
    static natural apply(T... x) {
        arguments args{ x... };
    return eval(args);
    }
};
template<typename f, typename... gs>
struct S {
    static natural eval(const arguments args) {
        arguments output{  gs::eval(args)... };
        return f::eval(output);
    }
    template<typename... T>
    static natural apply(T... x) {
        arguments args{ x... };
        return eval(args);
    }
};
template<natural n, natural i>
struct U {

    static natural eval(const arguments  args) {
        return args[i-1];
    }

    template<typename... T>
    static natural apply(T... x) {
        arguments args{ x... };
    return eval(args);
    }
};
template <typename f, typename g>
struct R {
    static natural eval(const  arguments  args) {
        natural size = args.size();
        natural y = args[size - 1];
        arguments f_args(args.begin(), --args.end());

        if (y == 0) {
            return f::eval(f_args);
        }
        else {
            arguments g_args(f_args);
            arguments n_args(f_args);
            g_args.resize(size+1);
            g_args[size - 1] = y - 1;
            n_args.push_back(y - 1); 
            g_args[size] = R< f,g >::eval(n_args);
            return g::eval(g_args);
        }
    }

    template<typename... T>
    static natural apply(T... x) {
        arguments args{ x... };
        return eval(args);
    }
};

template<typename f>
struct M {
    static natural eval(const arguments  args) {
        natural y = 0;
        natural size = args.size();
        arguments f_args(args.begin(), args.end());
        f_args.push_back(y);
        while(f::eval(f_args) != 0) {
            y++;
            f_args[size] = y;
            
        }
        return y;
    }
    template<typename... T>
    static natural apply(T... x) {
        arguments args{ x... };
        return eval(args);
    }
};



typedef S< R<Z,U<3,2> >, U<1,1>, U<1,1> > r_dec;
typedef N r_inc;
typedef S< N, Z > one;
typedef S < R < N, S<Z, U<3, 3> > >, U<1,1>, U<1,1> > NOT;
typedef R< U<1,1>, S<r_inc, U<3, 3> > > r_plus;
typedef R< U<1,1>, S<r_dec, U<3, 3> > > r_minus;
typedef R< Z, S< r_plus, U<3, 3>, U<3, 1> > > r_mul;
typedef R< one, S< r_mul, U<3, 3>, U<3, 1> > > r_pow;
typedef S< r_dec, S< M< S<r_minus, U<3,1>, S<r_mul, U<3, 2>, U<3, 3> > > >, S<r_inc, U<2, 1> >, U<2, 2> > > r_div; 
typedef S<r_minus, U<2,1>, S<r_mul, U<2,2>, r_div > > r_mod;

typedef S<S<NOT, NOT> , r_mul> AND;
typedef S<S<NOT, NOT> , r_plus> OR;
typedef S< S<NOT, NOT> ,r_minus > r_greater;
typedef S < S<NOT, NOT> , S<r_minus, U<2,2>, U<2, 1> > > r_less;
typedef S<AND, S<NOT, r_greater>, S<NOT, r_less> > r_equal;
typedef S<
R< S<r_greater, U<1,1>, one> , 
S< S< AND, S<r_mod, U<3,1>, U<3,2> > , U<3,3> >, U<3,1>, S<S<r_inc, r_inc> , U<3,2> >, U<3,3> > >,
U<1,1>, S<r_dec, S<r_div, U<1,1>, S<r_inc, one> > >
> isPrime;
typedef S< R<Z, S<r_plus, S<isPrime, U<3,2> >, U<3,3> > >, U<1,1>, S<r_inc, U<1,1> > > number_of_primes_r_less_than_n;

typedef S < M< S< r_greater, U<2,1>, S<number_of_primes_r_less_than_n, U<2,2> > > >, r_inc> nthPrime; 
typedef S< r_dec, M<S< S<NOT, r_mod> , U<3,2>, S<r_pow, U<3,1>, U<3,3> > > > > plog;




int main() {
    cout << r_plus::apply(4, 7) << endl;
    cout << r_minus::apply(7, 8) << endl;
    cout << r_div::apply(9, 14) << endl;
    cout << r_mod::apply(16, 4) << endl;
    cout << isPrime::apply(10) << endl;
    cout << isPrime::apply(11) << endl;

    for(natural i = 0; i < 10; i++) {
        cout << "nthPrime(" << i << ")=";
        cout << nthPrime::apply(i) << endl;
    }
    for(natural i = 1; i < 46; i++) {
        cout << "plog(2," << i <<")=";
        cout << plog::apply(2, i) << endl;
    }
    for(natural i = 1; i < 46; i++) {
        cout << "plog(5," << i <<")=";
        cout << plog::apply(5, i) << endl;
    }
}


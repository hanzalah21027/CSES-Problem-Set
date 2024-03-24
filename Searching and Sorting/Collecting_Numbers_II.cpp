#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

typedef long long ll;
typedef unsigned long long ull;
typedef long double lld;

#define F               first
#define S               second
#define ppb             pop_back
#define psb             push_back
#define eb              emplace_back
#define all(p)          p.begin(), p.end()
#define pii             pair<int, int>
#define pll             pair<ll, ll>
#define triplet         pair<int, pii>
#define nline           "\n"
#define bug(...)        __f(#__VA_ARGS__, __VA_ARGS__)
#define debug(x)     cerr << #x<<" : "; _print(x); cerr << endl;
#define mod             1000000007
#define MOD             998244353
#define inf             (1LL<<60)
#define PI              3.141592653589793238462
#define pair(i, j)        make_pair(i, j)
#define set_bits(x)     __builtin_popcountll(x)
#define precision(p)    cout << fixed << setprecision(p)

// greater<int>() -> For descending order in vectors.
// greater<int> -> For descending order in others.
// less_equal<int> -> For multiset in ascending order
// greater<int> -> For set in descending order
// greater_equal<int> -> For multiset in descending order
// less<int> -> For set in ascending order

typedef tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update> pbds; // find_by_order, order_of_key

void _print(ll t) {cerr << t;}
void _print(int t) {cerr << t;}
void _print(string t) {cerr << t;}
void _print(char t) {cerr << t;}
void _print(lld t) {cerr << t;}
void _print(double t) {cerr << t;}
void _print(ull t) {cerr << t;}

template <class T, class V> void _print(pair <T, V> p);
template <class T> void _print(vector <T> v);
template <class T> void _print(set <T> v);
template <class T, class V> void _print(map <T, V> v);
template <class T> void _print(multiset <T> v);
template <class T, class V> void _print(pair <T, V> p) {cerr << "{"; _print(p.ff); cerr << ","; _print(p.ss); cerr << "}";}
template <class T> void _print(vector <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(set <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(multiset <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T, class V> void _print(map <T, V> v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}
void _print(pbds v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}


mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
//----------------------------------------------------------------------------------------------------------------------------------------------
ll expo(ll a, ll b, ll m) {ll res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
ll mminvprime(ll &a, ll &b) {return expo(a, b - 2, b);}
vector<int> SPF(int n) {vector<int> lpf(n + 1); lpf[0] = lpf[1] = -1; for (int i = 2; i <= n; i++) lpf[i] = i; for (ll i = 2; i * i <= n; i++) {if (lpf[i] != i) {continue;} for (ll j = i * i; j <= n; j += i) lpf[j] = i;} return lpf;}
vector<bool> sieve(int n) {vector<bool> is_prime(n + 1, true); is_prime[0] = false; is_prime[1] = false; for (ll i = 2; i * i <= n; i++) {if (!is_prime[i]) {continue;} for (ll j = i * i; j <= n; j += i) is_prime[j] = false;} return is_prime;}
ll mod_add(ll &a, ll &b, ll &m) {return (a + b) % m;}
ll mod_mul(ll &a, ll &b, ll &m) {return (a * b) % m;}
ll mod_sub(ll &a, ll &b, ll &m) {return (a - b + m) % m;}
ll mod_div(ll &a, ll &b, ll &m) {return (a * mminvprime(b, m)) % m;}  //only for prime m
int getRandomNumber(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);}
//----------------------------------------------------------------------------------------------------------------------------------------------


inline ll power(ll a, ll b) {
    ll x = 1;
    while (b) {
        if (b & 1)  x *= a;
        a *= a;
        b >>= 1;
    }
    return x;
}


ll gcd(ll a, ll b) {
    if (a == 0) {
        return b;
    }
    return gcd(b % a, a);
}

ll lcm(ll a, ll b) {
    return (1LL * a * b) / gcd(a, b);
}

template<typename Arg1>
void __f(const char* name, Arg1&& arg1) {
    cerr << name << " : " << arg1 << endl;
}

template<typename Arg1, typename... Args>
void __f(const char* names, Arg1&& arg1, Args&&... args) {
    const char* comma = strchr (names + 1, ',');
    cerr.write(names, comma - names) << " : " << arg1 << " | ";
    __f(comma + 1, args...);
}



//##############################//
//#### Solution begins here ####//
//####   Author@Hanzalah    ####//
//##############################//

/*Our approach will be to construct array positions, which will store the index of all elements in the array ARR. 
We will find the total number of rounds of the current permutation using the same approach used in the previous Collecting Numbers 
problem approach. For each query, we are swapping two numbers placed at positions x and y. We need to consider four pairs 
to find the total rounds of the modified permutation. The four pairs are (ARR[x] - 1, ARR[x]), (ARR[x],  ARR[x] + 1), 
(ARR[y] - 1, ARR[y]) and (ARR[y],  ARR[y] + 1). Our approach will be to decrement the total number of rounds of the 
current permutation by the number of pairs having an index of the first value greater than the second value. 
Then we will swap the numbers placed at the positions x and y, and we will update the index of the number placed at x and y 
in the array positions. Finally, we will increment the total number of rounds by the number of pairs following the given 
conditions to obtain the total number of rounds of the modified permutation. Note that we will consider each pair no more 
than once to avoid duplicate values.*/

void solver() {
    int n, m;
    cin >> n >> m;

    vector<int> nums(n+1), idxs(n+1);
    for(int i = 1; i <= n; i++){
        cin >> nums[i];
        idxs[nums[i]] = i;
    }

    int round = 1;
    for(int i = 2; i <= n; i++){
        if(idxs[i] < idxs[i-1])     round++;
    }
    
    while(m--){
        int a, b;
        cin >> a >> b;   
        int numsa = nums[a];
        int numsb = nums[b];
        set<pii> s;

        if (numsa != 1)
            s.insert({numsa - 1, numsa});
        if (numsa != n)
            s.insert({numsa, numsa + 1});
        if (numsb != 1)
            s.insert({numsb - 1, numsb});
        if (numsb != n)
            s.insert({numsb, numsb + 1});

        for(auto it : s)   if(idxs[it.first] > idxs[it.second])    round--;
        
        swap(idxs[numsa], idxs[numsb]);
        swap(nums[a], nums[b]);

        for(auto it : s)   if(idxs[it.first] > idxs[it.second])    round++;
        cout << round << nline;
    }
}



int main() {
    ios_base::sync_with_stdio(0); cin.tie(0); cout.tie(0);
    //clock_t z = clock();
    ll t = 1;
    // cin >> t;
    while (t--) solver();
    // cerr << "Run Time : " << ((double)(clock() - z) / CLOCKS_PER_SEC) << endl;
}
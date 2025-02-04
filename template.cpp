#pragma GCC optimize("Ofast")
#pragma GCC optimize("unroll-loops")
#include<iostream>
#include<vector>
#include<cmath>
#include<algorithm>
#include<string>
#include<unordered_set>
#include<set>
#include<utility>
#include<iomanip>
#include<unordered_map>
#include<map>
#include<deque>
#include<list>
#include<stack>
#include<queue>
#include<cctype>
#include<climits>
#include<queue>
#include<deque>
#include<numeric>
#include<chrono>
#include<cfloat>
#include<bitset>
using namespace std;
using llu=unsigned long long;
using ll=long long;
using ld=long double;
using vll=vector<ll>;
using sl=set<ll>;
using msl=multiset<ll>;
using prq=priority_queue<ll>;
using prqi=priority_queue<ll,vector<ll>,greater<ll>>;
using ma=map<ll,ll>;
using vp=vector<pair<ll,ll>>;
using vvl=vector<vector<ll>>;
using sp=set<pair<ll,ll>>;
using msp=multiset<pair<ll,ll>>;
#define mod 1000000007
#define mod2 998244353
#define inf 9223372036854775807
#define nfs string::npos
#define count1(n) __builtin_popcountll(n)
#define mat(v,n,m) vector<vector<ll>>v(n,vector<ll>(m,0))
#define maxi(v) max_element(all(v))
#define mini(v) min_element(all(v))
#define lb(n) lower_bound(n)
#define ub(n) upper_bound(n)
#define lbd(v,n) lower_bound(all(v),n)
#define ubd(v,n) upper_bound(all(v),n)
#define fr(i,a,b) for(i=a;i<=b;i++)
#define fv(i,a,b) for(i=a;i>=b;i--)
#define f(i,n) for(i=0;i<n;i++)
#define fn(i,n) for(i=n-1;i>=0;i--)
#define pb push_back
#define eb emplace_back
#define mp make_pair
#define all(v) v.begin(),v.end()
#define g(v,n) vl v(n); f(_,n) cin>>v[_]
#define bs(n,x) bitset<n> (x).to_string()
#define invp(v,n) vp v;f(_,n){cin>>__;v.pb(mp(__,_+1));}
#define seev(v) for(auto ggg:v) cout<<ggg<<"-"
#define _print(v) for(auto ggg:v) cout<<ggg<<" "
#define inn(v,n) f(i,n)cin>>v[i];
#define endl "\n"
void yes(){cout<<"YES";}
void no(){cout<<"NO";}
struct custom_hash { static uint64_t splitmix64(uint64_t x) { x += 0x9e3779b97f4a7c15; x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9; x = (x ^ (x >> 27)) * 0x94d049bb133111eb; return x ^ (x >> 31); } size_t operator()(uint64_t x) const { static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count(); return splitmix64(x + FIXED_RANDOM); } };
ll gcd_dio(ll a,ll b,ll &x,ll &y)
{
    //x and y s/t ax+by=gcd(a,b)
    if(b==0)
    {
        x=1;
        y=0;
        return a;
    }
    ll x1,y1;
    ll d=gcd_dio(b,a%b,x1,y1);
    x=y1;
    y=x1-y1*(a/b);
    return d;
}
ll gcd(ll a,ll b)
{
    if(b==0)
    {
        return a;
    }
    ll d=gcd(b,a%b);
    return d;
}
ll lcm(ll a,ll b)
{
    return (a*b)/gcd(a,b);
}
ll inverse(ll a,ll m)
{
    ll x,y;
    ll g=gcd_dio(a,m,x,y);
    if(g!=1)
        return -1;
    else
    {
        x=(x%m+m)%m;
        return x;
    }
}
ll power(ll a,ll b)
{
    ll res=1;
    while(b>0)
    {
        if(b%2==1)
            res=(res*a)%inf;
        a=(a*a)%inf;
        b=b/2;
    }
    return res;
}
ll power(ll a,ll b,ll p)
{
    ll res=1;
    while(b>0)
    {
        if(b%2==1)
            res=(res*a)%p;
        a=(a*a)%p;
        b=b/2;
    }
    return res;
}
ll logg2(ll n)
{
    ll i;
    string s=bs(64,n);
    f(i,64)
        if(s[i]=='1')
            break;
    return 63-i;
}
ll todec(ll n,string s)
{
    ll i,k=0;
    f(i,n)
        if(s[i]=='1')
            k+=1LL<<(n-i-1);
    return k;
}
bool isprime(ll n)
{
    ll i;
    if(n==1)
        return false;
    for(i=2;i*i<=n;i++)
        if(n%i==0)
            return false;
    return true;
}
vll factors(ll n)
{
    ll i;vll v;
    for(i=1;i*i<=n;i++)
    {
        if(n%i==0)
        {
            if(i==n/i)
                v.pb(i);
            else
            {
                v.pb(i);
                v.pb(n/i);
            }
        }
    }
    sort(all(v));
    return v;
}
vll fact;
void fct()
{
    fact.resize(1000001);
    fact[0]=1;ll i;
    fr(i,1,1000000)
    fact[i]=((i%mod)*(fact[i-1]%mod))%mod;
}
ll nck(ll n,ll k)
{
    if(n>=k)
        return (((fact[n]*(inverse(fact[k],mod)))%mod)*inverse(fact[n-k],mod))%mod;
    else
        return 0;
}
ll crt(vll md,vll nm)
{
    ll i,p=1,q,ans=0,n=md.size();
    for(ll g:nm)
        p*=g;
    f(i,n)
    {
        q=p/nm[i];
        ans+=(md[i]*inverse(q,nm[i])*q)%p;
    }
    return ans%p;
}
vll prf;vll mob;
void sieve()
{
    prf.resize(1000001);
    mob.resize(1000001,1);
    ll i,j;
    for(i=2;i<=1000000;i++)
    {
        if(prf[i]==0)
        {
            for(j=i;j<=1000000;j+=i)
            {
                prf[j]=i;
                mob[j]=-mob[j];
                if(j%(i*i)==0)
                mob[j]=0;
            }
        }
    }
}
ma prime_factors(ll n,ma &mp)
{
    ll i=0;
    while(n%2==0)
    {
        mp[2]++;
        n/=2;
    }
    fr(i,3,sqrt(n)+1)
    {
        while(n%i==0)
        {
            mp[i]++;
            n/=i;
        }
    }
    if(n>2)
    {
        mp[n]++;
    }
    return mp;
}
bool vps(const pair<ll,ll> &a,const pair<ll,ll> &b)
{
    return (a.second<b.second);
}
bool fts(const pair<ll,ll> &a,const pair<ll,ll> &b)
{
    if(a.first!=b.first)
        return (a.first<b.first);
    return (a.second>b.second);
}
#ifndef DEBUG_TEMPLATE_CPP
#define DEBUG_TEMPLATE_CPP
// #define cerr cout
namespace __DEBUG_UTIL__
{
    using namespace std;
    /* Primitive Datatypes Print */
    void print(const char *x) { cerr << x; }
    void print(bool x) { cerr << (x ? "T" : "F"); }
    void print(char x) { cerr << '\'' << x << '\''; }
    void print(signed short int x) { cerr << x; }
    void print(unsigned short int x) { cerr << x; }
    void print(signed int x) { cerr << x; }
    void print(unsigned int x) { cerr << x; }
    void print(signed long int x) { cerr << x; }
    void print(unsigned long int x) { cerr << x; }
    void print(signed long long int x) { cerr << x; }
    void print(unsigned long long int x) { cerr << x; }
    void print(float x) { cerr << x; }
    void print(double x) { cerr << x; }
    void print(long double x) { cerr << x; }
    void print(string x) { cerr << '\"' << x << '\"'; }
    template <size_t N>
    void print(bitset<N> x) { cerr << x; }
    void print(vector<bool> v)
    { /* Overloaded this because stl optimizes vector<bool> by using
          _Bit_reference instead of bool to conserve space. */
        int f = 0;
        cerr << '{';
        for (auto &&i : v)
            cerr << (f++ ? "," : "") << (i ? "T" : "F");
        cerr << "}";
    }
    /* Templates Declarations to support nested datatypes */
    template <typename T>
    void print(T &&x);
    template <typename T>
    void print(vector<vector<T>> mat);
    template <typename T, size_t N, size_t M>
    void print(T (&mat)[N][M]);
    template <typename F, typename S>
    void print(pair<F, S> x);
    template <typename T, size_t N>
    struct Tuple;
    template <typename T>
    struct Tuple<T, 1>;
    template <typename... Args>
    void print(tuple<Args...> t);
    template <typename... T>
    void print(priority_queue<T...> pq);
    template <typename T>
    void print(stack<T> st);
    template <typename T>
    void print(queue<T> q);
    /* Template Datatypes Definitions */
    template <typename T>
    void print(T &&x)
    {
        /*  This works for every container that supports range-based loop
            i.e. vector, set, map, oset, omap, dequeue */
        int f = 0;
        cerr << '{';
        for (auto &&i : x)
            cerr << (f++ ? "," : ""), print(i);
        cerr << "}";
    }
    template <typename T>
    void print(vector<vector<T>> mat)
    {
        int f = 0;
        cerr << "\n~~~~~\n";
        for (auto &&i : mat)
        {
            cerr << setw(2) << left << f++, print(i), cerr << "\n";
        }
        cerr << "~~~~~\n";
    }
    template <typename T, size_t N, size_t M>
    void print(T (&mat)[N][M])
    {
        int f = 0;
        cerr << "\n~~~~~\n";
        for (auto &&i : mat)
        {
            cerr << setw(2) << left << f++, print(i), cerr << "\n";
        }
        cerr << "~~~~~\n";
    }
    template <typename F, typename S>
    void print(pair<F, S> x)
    {
        cerr << '(';
        print(x.first);
        cerr << ',';
        print(x.second);
        cerr << ')';
    }
    template <typename T, size_t N>
    struct Tuple
    {
        static void printTuple(T t)
        {
            Tuple<T, N - 1>::printTuple(t);
            cerr << ",", print(get<N - 1>(t));
        }
    };
    template <typename T>
    struct Tuple<T, 1>
    {
        static void printTuple(T t) { print(get<0>(t)); }
    };
    template <typename... Args>
    void print(tuple<Args...> t)
    {
        cerr << "(";
        Tuple<decltype(t), sizeof...(Args)>::printTuple(t);
        cerr << ")";
    }
    template <typename... T>
    void print(priority_queue<T...> pq)
    {
        int f = 0;
        cerr << '{';
        while (!pq.empty())
            cerr << (f++ ? "," : ""), print(pq.top()), pq.pop();
        cerr << "}";
    }
    template <typename T>
    void print(stack<T> st)
    {
        int f = 0;
        cerr << '{';
        while (!st.empty())
            cerr << (f++ ? "," : ""), print(st.top()), st.pop();
        cerr << "}";
    }
    template <typename T>
    void print(queue<T> q)
    {
        int f = 0;
        cerr << '{';
        while (!q.empty())
            cerr << (f++ ? "," : ""), print(q.front()), q.pop();
        cerr << "}";
    }
    /* Printer functions */
    void printer(const char *) {} /* Base Recursive */
    template <typename T, typename... V>
    void printer(const char *names, T &&head, V &&...tail)
    {
        /* Using && to capture both lvalues and rvalues */
        int i = 0;
        for (size_t bracket = 0; names[i] != '\0' and (names[i] != ',' or bracket != 0); i++)
            if (names[i] == '(' or names[i] == '<' or names[i] == '{')
                bracket++;
            else if (names[i] == ')' or names[i] == '>' or names[i] == '}')
                bracket--;
        cerr.write(names, i) << " = ";
        print(head);
        if (sizeof...(tail))
            cerr << " ||", printer(names + i + 1, tail...);
        else
            cerr << "]\n";
    }
    /* PrinterArr */
    void printerArr(const char *) {} /* Base Recursive */
    template <typename T, typename... V>
    void printerArr(const char *names, T arr[], size_t N, V... tail)
    {
        size_t ind = 0;
        for (; names[ind] and names[ind] != ','; ind++)
            cerr << names[ind];
        for (ind++; names[ind] and names[ind] != ','; ind++)
            ;
        cerr << " = {";
        for (size_t i = 0; i < N; i++)
            cerr << (i ? "," : ""), print(arr[i]);
        cerr << "}";
        if (sizeof...(tail))
            cerr << " ||", printerArr(names + ind + 1, tail...);
        else
            cerr << "]\n";
    }
}
#ifndef ONLINE_JUDGE
#define debug(...) std::cerr << __LINE__ << ": [", __DEBUG_UTIL__::printer(#__VA_ARGS__, __VA_ARGS__)
#define debugArr(...) std::cerr << __LINE__ << ": [", __DEBUG_UTIL__::printerArr(#__VA_ARGS__, __VA_ARGS__)
#else
#define debug(...)
#define debugArr(...)
#endif
#endif
vll parent(1e3+1);
vll size_(1e3+1);
class DSU
{
    public: 
    void create(ll n)    // N --> Max Element to be stored in DSU
    {
        parent.resize(n);
        size_.resize(n);
    }
    void make(ll n)
    {
        parent[n]=n;
        size_[n]=1;
    }
    ll find(ll n)
    {
        if(parent[n]==n)return n;
        else return parent[n]=find(parent[n]);
    }
    void Union(ll a,ll b)
    {
        a=find(a);
        b=find(b);
        if(b!=a)
        {
            if(size_[b]>size_[a])
                swap(a,b);
            parent[b]=a;
            size_[a]+=size_[b];
        }
    }
};
vector<int>visited;
vector<vector<int>>graph;
vector<int>col;
vector<pair<int,int>>movements={{0,1},{0,-1},{1,0},{-1,0}};
bool isValid(int i,int j,int n,int m)
{
    return (i>=0&&i<n&&j>=0&&j<m&&(graph[i][j]!='#'));
}
void solve(ll tc)
{
    ll n,m,k=0,j=0,i=0,x=0,y=0,z=0,p=0,q=0,l=0,sum=0,temp=-1,flag=0,a=0,b=0,c=0,d=0,r=0,mn=inf,mx=-inf,_,__,mid;
    string s1,s2,s3,s;char ch;
    
}

signed main()
{
    #ifndef ONLINE_JUDGE
    clock_t T = clock();
    #endif
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    cout.tie(NULL);
    ll t=1;
    cin>>t;
    ll tt=t;
    while(t--)
    {
        ll testcase_no=tt-t;
        debug((testcase_no));
        solve(t);
        cout<<endl;
    }
    #ifndef ONLINE_JUDGE
    cout << "\nTime taken: " << ((float)(clock() - T))/CLOCKS_PER_SEC << " seconds";
    #endif
    return 0;
}
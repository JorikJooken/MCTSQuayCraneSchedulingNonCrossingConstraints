#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <chrono>

using namespace __gnu_pbds;
using namespace std;

long long inf=1e18;
double eps=1e-12;

int width;
int n, m;
vector<int> p;

long long bestValue;
vector<int> bestSolution;

long long currentRDT;
vector<int> currentSolution;
vector< vector<long long> > currentTimes;

double allowedTimeInSeconds;

random_device rd;

int randIntegralBetween(int lo, int hi)
{
    mt19937 gen(rd());
    uniform_int_distribution<> dis(lo,hi);
    return dis(gen);
}

double randDoubleZeroOne()
{
    return 1.0*randIntegralBetween(0, INT_MAX)/INT_MAX;
}

double randDouble(double lo, double hi)
{
    return lo+randDoubleZeroOne()*(hi-lo);
}

void readProblemInstance() // from standard input
{
    scanf("%d %d", &n, &m); // n containers, m cranes
    p.assign(n,-1);
    for(int i=0; i<n; i++) scanf("%d", &p[i]);
}

void makeChoice(int index, int i)
{
    currentSolution[index]=i;
    for(int j=0; j<m; j++)
    {
        if(index==0) currentTimes[index][j]=0;
        else currentTimes[index][j]=currentTimes[index-1][j];
    }
    currentTimes[index][i]+=p[index];
    currentRDT-=p[index];
    if(i==0) currentRDT+=1LL*p[index]*m;
    for(int j=i-1; j>=0; j--)
    {
        if(currentTimes[index][j]<currentTimes[index][j+1])
        {
            long long diff=currentTimes[index][j+1]-currentTimes[index][j];
            currentRDT-=diff;
            if(j==0)
            {
                currentRDT+=diff*m;
            }
            currentTimes[index][j]=currentTimes[index][j+1];
        }
        else break;
    }
}

bool positiveOverlap(long long start1, long long end1, long long start2, long long end2)
{
    long long from=max(start1,start2);
    long long to=min(end1,end2);
    if(from<to) return true;
    return false;
}

bool satisfiesNonSandwichConstraints(vector<int> &sol)
{
    vector<long long> startTimes(n,0);
    vector<long long> foo(m,0);
    vector< vector<long long> > earliest(n, foo);
    for(int i=0; i<n; i++)
    {
        if(i-1>=0)
        {
            for(int j=0; j<m; j++)
            {
                earliest[i][j]=earliest[i-1][j];
            }
        }
        startTimes[i]=earliest[i][sol[i]];
        earliest[i][sol[i]]+=p[i];
        for(int j=sol[i]-1; j>=0; j--)
        {
            if(earliest[i][j]>=earliest[i][j+1]) break;
            earliest[i][j]=earliest[i][j+1];
        }
        for(int stepsBack=1; stepsBack<=m-2 && stepsBack<=sol[i]-1 && i-stepsBack>=0; stepsBack++)
        {
            if(sol[i-stepsBack]>=sol[i]) continue;
            if(sol[i]-sol[i-stepsBack]<=stepsBack) continue;
            if(positiveOverlap(startTimes[i], startTimes[i]+p[i], startTimes[i-stepsBack], startTimes[i-stepsBack]+p[i-stepsBack])) return false;
        }
    }
    return true;
}

bool fuzzy_eq(double a, double b)
{
    return fabs(a-b)<=eps;
}

vector<long long> sum;
void QCSNC_two(int from, int to)
{
    int n_pseudo=to-from+1;
    long long T=sum[to+1]-sum[from];
    vector< vector<long long> > A(n_pseudo+1, vector<long long>(T+1,inf));
    vector< vector< pair<long long, long long> > > prev_ptr(n_pseudo+1, vector< pair<long long, long long> >(T+1)); // for recovering actual solution instead of only value
    vector< vector<int> > which_crane(n_pseudo+1, vector<int>(T+1,-1));
    A[0][0]=0;
    for(int i=1; i<=n_pseudo; i++)
    {
        for(long long w2=0; w2<=T; w2++)
        {
            long long option1=max(A[i-1][w2],w2)+p[from+i-1];
            long long option2=inf;
            if(w2>=p[from+i-1]) option2=A[i-1][w2-p[from+i-1]];
            if(option1<=option2)
            {
                A[i][w2]=option1;
                prev_ptr[i][w2]=make_pair(i-1,w2);
                which_crane[i][w2]=bestSolution[from];
            }
            else
            {
                A[i][w2]=option2;
                prev_ptr[i][w2]=make_pair(i-1,w2-p[from+i-1]);
                which_crane[i][w2]=bestSolution[to];
            }
        }
    }
    // reconstruct actual solution
    vector<int> assignment(n_pseudo,-1);
    long long ptr1=n_pseudo;
    pair<long long, long long> to_minimize=make_pair(inf,-1);
    for(long long w2=0; w2<=T; w2++)
    {
        to_minimize=min(to_minimize,make_pair(max(A[ptr1][w2],w2),w2));
    }
    long long ptr2=to_minimize.second;
    while(ptr1>0)
    {
        assignment[ptr1-1]=which_crane[ptr1][ptr2];
        pair<long long, long long> new_ptrs=prev_ptr[ptr1][ptr2];
        ptr1=new_ptrs.first;
        ptr2=new_ptrs.second;
    }
    for(int i=0; i<n_pseudo; i++)
    {
        bestSolution[from+i]=assignment[i];
    }
}

void calcSolution()
{
    // do DP
    sum.assign(n+1,0);
    vector<long long> maxjob(n+1,0);
    vector< vector<long long> > A(m+1, vector<long long>(n+1,0));
    vector< vector<long long> > previous_i(m+1, vector<long long>(n+1,0)); // for storing backpointers to reconstruct actual solution instead of only value
    maxjob[1]=p[0];
    for(int i=1; i<=n; i++) sum[i]=sum[i-1]+p[i-1];
    for(int i=1; i<=n; i++) A[1][i]=sum[i];
    for(int i=2; i<=n; i++) maxjob[i]=max(maxjob[i],1LL*p[i-1]);
    for(int k=2; k<=m; k++)
    {
        for(int i=k; i<=n; i++)
        {
            A[k][i]=inf;
            if(k==i)
            {
                A[k][i]=maxjob[i];
                previous_i[k][i]=i-1;
            }
            else
            {
                int lp=k-1;
                int rp=i-1;
                while(rp-lp>1)
                {
                    int mp=(lp+rp)/2;
                    if(A[k-1][mp]==sum[i]-sum[mp])
                    {
                        rp=mp;
                        break;
                    }
                    else
                    {
                        if(A[k-1][mp]>sum[i]-sum[mp])
                        {
                            rp=mp;
                        }
                        else
                        {
                            lp=mp;
                        }
                    }
                }
                if(A[k-1][rp]<=sum[i]-sum[lp])
                {
                    A[k][i]=A[k-1][rp];
                    previous_i[k][i]=rp;
                }
                else
                {
                    A[k][i]=sum[i]-sum[lp];
                    previous_i[k][i]=lp;
                }
            }
        }
    }
    bestValue=A[m][n];
    // reconstruct actual solution
    int ptr1=m;
    int ptr2=n;
    while(ptr1>1)
    {
        int prev_i=previous_i[ptr1][ptr2];
        for(int i=prev_i+1; i<=ptr2; i++)
        {
            bestSolution[i-1]=ptr1-1;
        }
        ptr1--;
        ptr2=prev_i;
    }
    // merge groups of 2 cranes together
    int num_groups=0;
    vector<int> start_index;
    vector<int> finish_index;
    vector<long long> S;
    for(int i=0; i<n; i++)
    {
        if(i==0 || bestSolution[i]!=bestSolution[i-1])
        {
            start_index.push_back(i);
            finish_index.push_back(i);
            S.push_back(0);
            num_groups++;
        }
        finish_index[finish_index.size()-1]=i;
        S[S.size()-1]+=p[i];
    } 
    long long AT=sum[n]/m;
    set<int> phi;
    set<int> omega;
    for(int k=0; k<S.size(); k++)
    {
        if(S[k]>AT)
        {
            phi.insert(k);
        }
    }
    while(phi.size()>0)
    {
        pair<long long, int> to_maximize=make_pair(-inf,0);
        for(int k : phi)
        {
            to_maximize=max(to_maximize,make_pair(S[k],k));
        }
        int k=to_maximize.second;
        int l=-1;
        if(k==0)
        {
            l=k+1;
        }
        else if(k==S.size()-1)
        {
            l=k-1;
        }
        else
        {
            if(!(k-1>=0 && k-1<S.size()) || omega.count(k-1)>0) l=k+1;
            else if(!(k+1>=0 && k+1<S.size()) || omega.count(k+1)>0) l=k-1;
            else if(S[k-1]<S[k+1])
            {
                l=k-1;
            }
            else
            {
                l=k+1;
            }
        }
        if(!(0<=l && l<S.size()) || omega.count(l)>0)
        {
            phi.erase(k);   
        }
        else
        {
            QCSNC_two(min(start_index[l],start_index[k]),max(finish_index[l],finish_index[k]));
            phi.erase(k);
            phi.erase(l);
            omega.insert(k);
            omega.insert(l);
        }
    }
}

int main()
{
    auto start=chrono::high_resolution_clock::now();
    bestValue=inf;
    readProblemInstance();
    /*for(int i=0; i<n; i++)
    {
        cerr << i << " " << p[i] << endl;
    }*/
    bestSolution.assign(n,0);
    currentSolution.assign(n,0);
    vector<long long> foo(m,0);
    currentTimes.assign(n+1,foo);
    calcSolution();
    bestValue=0;
    auto stop=chrono::high_resolution_clock::now();
    auto duration = chrono::duration_cast<chrono::milliseconds>(stop-start);
    cout << "The execution time of the program was (in ms): " << duration.count() << endl;
    if(!satisfiesNonSandwichConstraints(bestSolution))
    {
        cout << "The produced solution is not feasible!" << endl;
        return 0;
    }
    for(int i=0; i<n; i++)
    {
        makeChoice(i,bestSolution[i]);
        cout << "Assign container " << i << " to crane " << bestSolution[i] << " from time slot " << currentTimes[i][bestSolution[i]]-p[i] << " until " <<  currentTimes[i][bestSolution[i]] << endl;
        bestValue=max(bestValue,currentTimes[i][bestSolution[i]]);
    }
    cout << "Best found solution has a value of: " << bestValue << endl;
    return 0;
}

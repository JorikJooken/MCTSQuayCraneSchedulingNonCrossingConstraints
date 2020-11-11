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

void calcSolution()
{
    long long sum_processing_times=0;
    for(int i=0; i<n; i++) sum_processing_times+=p[i];
    vector<double> new_p(n+1,0.0);
    for(int i=0; i<n; i++) new_p[i+1]=1.0*p[i]/sum_processing_times;

    int k=(m-1)/2;
    vector<int> j(k+2,0); // holds are 1-indexed
    
    double sum=0;
    int q=1;
    for(int i=1; i<=n && q<=k; i++)
    {
        long long numerator=2*q;
        long long denominator=m+1;
        double frac=1.0*numerator/denominator;
        if(sum<frac-eps && frac <= (sum+new_p[i])+eps)
        {
            j[q]=i;
            q++;
        }
        sum+=new_p[i];
    }
    double p_k_n=0;
    for(int i=j[k]+1; i<=n; i++)
    {
        p_k_n+=new_p[i];
    }
    int currentCrane=0;
    if(p_k_n<=(2.0/(m+1))+eps)
    {
        for(int i=0; i<n; i++) // take care of H(k,n)
        {
            bestSolution[i]=m-1;
        }
        for(int i=0; i<=k-1; i++)
        {
            int start=j[i]+1;
            int finish=j[i+1]-1;
            for(int x=start; x<=finish; x++)
            {
                bestSolution[x-1]=currentCrane;
            }
            currentCrane++;
            bestSolution[j[i+1]-1]=currentCrane;
            currentCrane++;
        }
        map<int, long long> crane_to_sum;
        for(int i=0; i<n; i++)
        {
            crane_to_sum[bestSolution[i]]+=p[i];
        }
        long long maxx=-1;
        for(auto it = crane_to_sum.begin(); it != crane_to_sum.end(); it++)
        {
            maxx=max(maxx,it->second);
        }
        bestValue=maxx;
    }
    else
    {
        sum=0;
        for(int i=j[k]+1; i<=n; i++)
        {
            double frac=0.5*p_k_n;
            if(sum<frac-eps && frac<=sum+new_p[i]+eps)
            {
                j[k+1]=i;
                break;
            }
            sum+=new_p[i];
        }
        for(int i=0; i<n; i++) // take care of H(k,n)
        {
            bestSolution[i]=m-1;
        }
        for(int i=0; i<=k; i++)
        {
            int start=j[i]+1;
            int finish=j[i+1]-1;
            for(int x=start; x<=finish; x++)
            {
                bestSolution[x-1]=currentCrane;
            }
            currentCrane++;
            bestSolution[j[i+1]-1]=currentCrane;
            currentCrane++;
        }

        double p_k_k_plus_one=0.0;
        for(int i=j[k]+1; i<=j[k+1]-1; i++)
        {
            p_k_k_plus_one+=new_p[i];
        }
        double p_k_plus_one_n=0.0;
        for(int i=j[k+1]+1; i<=n; i++)
        {
            p_k_plus_one_n+=new_p[i];
        }
        if(fuzzy_eq(p_k_k_plus_one+new_p[j[k+1]],0.5*p_k_n))
        {
            int idx1=j[k+1]-1;
            if(idx1-1>=0 && j[k]+1<=j[k+1]-1)
            {
                bestSolution[idx1]=bestSolution[idx1-1];
            }
        }
        else if(p_k_k_plus_one+new_p[j[k+1]]>0.5*p_k_n+eps)
        {
            pair<double, int> to_minimize=make_pair(inf,-1);
            for(int q=1; q<=k+1; q++)
            {
                sum=new_p[j[q]];
                for(int i=j[q-1]+1; i<=j[q]-1; i++)
                {
                    sum+=new_p[i];
                }
                to_minimize=min(to_minimize,make_pair(sum,q));
            }
            double lhs=to_minimize.first;
            double rhs=new_p[j[k+1]];
            for(int i=j[k+1]+1; i<=n; i++)
            {
                rhs+=new_p[i];
            }
            if(lhs<=rhs+eps)
            {
                int r=to_minimize.second;
                int idx1=j[r]-1;
                if(idx1-1>=0 && j[r-1]+1<=j[r]-1)
                {
                    bestSolution[idx1]=bestSolution[idx1-1];
                }
            }
            else
            {
                int idx1=j[k+1]-1;
                if(idx1+1<n && j[k+1]+1<=n)
                {
                    bestSolution[idx1]=bestSolution[idx1+1];
                }
            }
        }
        map<int, long long> crane_to_sum;
        for(int i=0; i<n; i++)
        {
            crane_to_sum[bestSolution[i]]+=p[i];
        }
        long long maxx=-1;
        for(auto it = crane_to_sum.begin(); it != crane_to_sum.end(); it++)
        {
            maxx=max(maxx,it->second);
        }
        bestValue=maxx;
    }
}

int main()
{
    auto start=chrono::high_resolution_clock::now();
    bestValue=inf;
    readProblemInstance();
    bestSolution.assign(n,0);
    currentSolution.assign(n,0);
    vector<long long> foo(m,0);
    currentTimes.assign(n+1,foo);
    calcSolution();
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
    }
    cout << "Best found solution has a value of: " << bestValue << endl;
    return 0;
}

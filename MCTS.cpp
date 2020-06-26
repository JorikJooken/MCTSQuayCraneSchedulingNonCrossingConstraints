#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <chrono>

using namespace __gnu_pbds;
using namespace std;

long long inf=1e18;
double eps=1e-9;

int width;
int n, m;
vector<int> p;
vector<long long> remainingSum;
vector<long long> suffixMax;

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


struct node
{
    vector<node*> children;
    double value;
    long long amountVisited;
    bool blocked;
    int numBlockedChildren;
    node* parent;
    node()
    {
        children.assign(m,NULL);
        value=inf;
        amountVisited=0;
        blocked=false;
        numBlockedChildren=0;
        parent=NULL;
    }
};
node* root;

void readParameters()
{
    ifstream inFile;
    inFile.open("MCTSParameters.txt");
    inFile >> allowedTimeInSeconds;
    inFile >> width;
    inFile.close();
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

long long solutionCompleted()
{
    if(currentTimes[n-1][0] < bestValue && satisfiesNonSandwichConstraints(currentSolution))
    {
        bestValue=currentTimes[n-1][0];
        bestSolution=currentSolution;
    }
    return currentTimes[n-1][0];
}

long long calcLowerBound(int index, bool useCurrentRDT=false)
{
    if(index>=n-1) return currentTimes[index][0];
    long long lb1=currentTimes[index][m-1];
    lb1+=suffixMax[index+1];

    long long lb2=currentTimes[index][0];
    long long totalTimeToDistribute=remainingSum[index+1];
    long long RDT=0;
    if(!useCurrentRDT)
    {
        for(int i=1; i<m; i++)
        {
            RDT+=currentTimes[index][0]-currentTimes[index][i];
        }
    }
    else
    {
        RDT=currentRDT;
    }
    if(totalTimeToDistribute>RDT)
    {
        long long denominator=min(m,n-index-1);
        lb2+=(totalTimeToDistribute-RDT+denominator-1)/denominator;
    }
    return max(lb1,lb2);
}

long long completePartialSolution(int index)
{
    if(index>=n) return solutionCompleted();
    pair<long long, int> bestFit=make_pair(inf,-1);
    int start=max(0,m-(n-index));
    int finish=min(m-1,index);
    for(int assignment=start; assignment<=finish; assignment++) // complexity can be improved.
    {
        long long currentRDTBeforeDestroying=currentRDT;
        makeChoice(index, assignment);
        currentRDT=currentRDTBeforeDestroying;
        bestFit=min(bestFit, make_pair(calcLowerBound(index), assignment));
    }
    makeChoice(index, bestFit.second);
    return completePartialSolution(index+1);
}

void cascadingBlock(node* node)
{
    if(node->blocked) return;
    node->blocked=true;
    if(node->parent != NULL)
    {
        node->parent->numBlockedChildren += 1;
        if(node->parent->numBlockedChildren==m) cascadingBlock(node->parent);
    }
}

int lastLevelCut=0;
vector<node*> lastLevel;
// inf means the lower bound is too high
// -1 means some child returned inf
long long buildSolution(int index, node* currentNode)
{
    if(index>=n)
    {
        return solutionCompleted();
    }
    
    if(index>0)
    {
        long long atLeast = calcLowerBound(index-1,true);
        if(atLeast>=bestValue)
        {
            currentNode->value=inf;
            return inf;
        }
    }
    int start=max(0,m-(n-index));
	int finish=min(m-1,index);
    if(index>=lastLevelCut)
    {
        vector< pair<double, int> > sortedValues;
        int amountEligible=0;
        for(int i=start; i<=finish; i++)
        {
            if(((i==0) || (index>0 && i-1>=0 && currentTimes[index-1][i-1]>currentTimes[index-1][i])) && (currentNode->children[i]==NULL || !currentNode->children[i]->blocked))
            {
                amountEligible++;
            }
            else continue;
            if(currentNode->children[i] != NULL)
            {
                double value=currentNode->children[i]->value;
                sortedValues.push_back(make_pair(value,i));
            }
        }
        sort(sortedValues.begin(),sortedValues.end());
        
        vector<double> inverseRank(m,-1);
        for(int i=0; i<sortedValues.size(); i++)
        {
            inverseRank[sortedValues[i].second]=sortedValues.size()-i;
        }
        vector<double> childrenScores;
        double normalizationFactor=0;
        for(int i=start; i<=finish; i++)
        {
            if(!(((i==0) || (index>0 && i-1>=0 && currentTimes[index-1][i-1]>currentTimes[index-1][i])) && (currentNode->children[i]==NULL || !currentNode->children[i]->blocked)))
            {
                continue;
            }
            if(currentNode->children[i] != NULL)
            {
                double score=inverseRank[i];
                childrenScores.push_back(score);
                normalizationFactor+=score;
            }
        }
        
        int scorePtr=0;
        double sumOfScores=0;
        pair<double, int> toMaximize=make_pair(-inf,-1);
        for(int i=start; i<=finish; i++)
        {
            if(!(((i==0) || (index>0 && i-1>=0 && currentTimes[index-1][i-1]>currentTimes[index-1][i])) && (currentNode->children[i]==NULL || !currentNode->children[i]->blocked)))
            {
                continue;
            }
            if(currentNode->children[i] != NULL)
            {
                childrenScores[scorePtr]/=normalizationFactor;
                childrenScores[scorePtr]+=sqrt(2*log(currentNode->amountVisited)/currentNode->children[i]->amountVisited);
                toMaximize=max(toMaximize,make_pair(childrenScores[scorePtr],i));
                sumOfScores+=childrenScores[scorePtr];
                scorePtr++;
            }
        }
        scorePtr=0;
        vector<double> percentages(m);
        for(int i=0; i<m; i++)
        {
            if(!(((i==0) || (index>0 && i-1>=0 && currentTimes[index-1][i-1]>currentTimes[index-1][i])) && (currentNode->children[i]==NULL || !currentNode->children[i]->blocked) && start <= i && i <= finish))
            {
                percentages[i]=0.0;
            }
            else
            {
                if(currentNode->children[i] != NULL)
                {
                    percentages[i]=(1.0*childrenScores.size()/amountEligible)*childrenScores[scorePtr]/sumOfScores;
                    scorePtr++;
                }
                else
                {
                    percentages[i]=1.0/amountEligible;
                }
            }
            if(i-1>=0) percentages[i]+=percentages[i-1];
        }
        if(abs(1-percentages[m-1]) > eps) return inf; // this means no child can be explored    
        percentages[m-1]=1.0; // avoid potential numerical errors
                

        double randNumber=randDoubleZeroOne();
        for(int i=0; i<m; i++)
        {
            if(randNumber<=percentages[i] && ((i==0 && randNumber != 0) || percentages[i-1]<randNumber))
            {
                if(currentNode->children[i]!=NULL) // choose child deterministically
                {
                    i=toMaximize.second;
                }
                makeChoice(index, i);   
                long long ret;
                if(currentNode->children[i] != NULL)
                {
                    ret=buildSolution(index+1, currentNode->children[i]);
                }
                else
                {
                    ret=completePartialSolution(index+1);
                    currentNode->children[i] = new node();
                    currentNode->children[i]->value=ret;
                    currentNode->children[i]->amountVisited=1;
                    currentNode->children[i]->parent=currentNode;
                }
                if(ret==-1)
                {
                    return ret;
                }
                if(ret==inf)
                {
                    cascadingBlock(currentNode->children[i]);
                    return -1;
                }
                currentNode->value += 1.0*ret/currentNode->amountVisited;
                currentNode->value *= (1.0*currentNode->amountVisited)/(currentNode->amountVisited+1);
                currentNode->amountVisited++;
                return ret;
            }
        }
    }
    else
    {
        vector< pair<double, int> > sortedValues;
        for(int i=start; i<=finish; i++)
        {
            if(currentNode->children[i] != NULL && !currentNode->children[i]->blocked)
            {
                double value=currentNode->children[i]->value;
                sortedValues.push_back(make_pair(value,i));
            }
        }
        sort(sortedValues.begin(),sortedValues.end());
        
        vector<double> inverseRank(m,-1);
        for(int i=0; i<sortedValues.size(); i++)
        {
            inverseRank[sortedValues[i].second]=sortedValues.size()-i;
        }
        vector<double> childrenScores;
        double normalizationFactor=0;
        for(int i=start; i<=finish; i++)
        {
            if(currentNode->children[i] != NULL  && !currentNode->children[i]->blocked)
            {
                double score=inverseRank[i];
                childrenScores.push_back(score);
                normalizationFactor+=score;
            }
        }
        
        pair<double, int> toMaximize=make_pair(-inf,-1);
        double sumOfScores=0;
        int scorePtr=0;
        for(int i=start; i<=finish; i++)
        {
            if(currentNode->children[i] != NULL  && !currentNode->children[i]->blocked)
            {
                childrenScores[scorePtr]/=normalizationFactor;
                childrenScores[scorePtr]+=sqrt(2*log(currentNode->amountVisited)/currentNode->children[i]->amountVisited);
                toMaximize=max(toMaximize,make_pair(childrenScores[scorePtr],i));
                sumOfScores+=childrenScores[scorePtr];
                scorePtr++;
            }
        }

        scorePtr=0;
        vector<double> percentages(m);
        for(int i=0; i<m; i++)
        {
            if(currentNode->children[i] != NULL && !currentNode->children[i]->blocked && start <= i && i <= finish)
            {
                percentages[i]=childrenScores[scorePtr]/sumOfScores;
                scorePtr++;
            }
            else
            {
                percentages[i]=0;
            }
            if(i-1>=0) percentages[i]+=percentages[i-1];
        }
        percentages[m-1]=1.0; // avoid potential numerical errors
        if(abs(1-percentages[m-1]) > eps) return inf; // this means no child can be explored 

        double randNumber=randDoubleZeroOne();
        for(int i=0; i<m; i++)
        {
            if(randNumber<=percentages[i] && ((i==0 && randNumber !=0) || percentages[i-1]<randNumber))
            {
                i=toMaximize.second;
                makeChoice(index, i);
                long long ret=buildSolution(index+1, currentNode->children[i]);
                if(ret==-1)
                {
                    return ret;
                }
                if(ret==inf)
                {
                    cascadingBlock(currentNode->children[i]);
                    return -1;
                }
                currentNode->value += 1.0*ret/currentNode->amountVisited;
                currentNode->value *= (1.0*currentNode->amountVisited)/(currentNode->amountVisited+1);
                currentNode->amountVisited++;
                return ret;
            }
        }
    }
    cout << "An error occured. This code should never be executed." << endl;
}

long long generateSingleSample()
{
    currentSolution.assign(n,-1);
    vector<long long> foo(m,0);
    currentTimes.assign(n,foo);
    currentRDT=0;
    if(root->blocked) return inf;
    return buildSolution(0, root);
}

void performCut()
{
    priority_queue< pair<double, node*> > pq;
    for(node* parentPtr : lastLevel)
    {
        parentPtr->numBlockedChildren=m;
        for(int i=0; i<m; i++)
        {
            node* child=parentPtr->children[i];
            if(child==NULL)
            {
                continue;
            }
            child->blocked=true;
            pq.push(make_pair(child->value, child));
            if(pq.size()>width) pq.pop();
        }
    }
    vector<node*> newLastLevel;
    while(!pq.empty())
    {
        pair<double, node*> top=pq.top();
        pq.pop();
        node* nd=top.second;
        newLastLevel.push_back(nd);
        nd->blocked=false;
        nd->parent->numBlockedChildren -= 1;
    }
    for(node* parentPtr : lastLevel)
    {
        if(parentPtr->numBlockedChildren==m) cascadingBlock(parentPtr);
    }
    lastLevel=newLastLevel;
}

void searchLoop()
{
    chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
    root = new node();
    lastLevel.push_back(root);
    while(true)
    {
        generateSingleSample();
        if(root->blocked)
        {
            break;
        }
        chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        double elapsedTime=chrono::duration_cast<std::chrono::microseconds>(end - begin).count()/1000000.0;
        if(elapsedTime>=allowedTimeInSeconds) return;
        if(elapsedTime>=(1.0*(lastLevelCut+1)/n)*allowedTimeInSeconds)
        {
            performCut();
            lastLevelCut++;
        }
    }
}

void precompute()
{
    suffixMax.assign(n,0);
    remainingSum.assign(n,0);
    for(int i=n-1; i>=0; i--)
    {
        remainingSum[i]+=p[i];
        suffixMax[i]=p[i];
        if(i+1<n)
        {
            remainingSum[i]+=remainingSum[i+1];
            suffixMax[i]=max(suffixMax[i],suffixMax[i+1]);
        }
    }
}

int main()
{
    bestValue=inf;
    readParameters();
    readProblemInstance();
    precompute();
    searchLoop();
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

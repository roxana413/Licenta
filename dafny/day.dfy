datatype Job = Pair(jobStart: int, jobEnd: int, profit: int)

predicate JobComparator(job1: Job, job2: Job)
{
    job1.jobEnd <= job2.jobEnd
}
predicate validJob(job: Job)
{
    job.jobStart < job.jobEnd && job.profit >= 0
}

predicate validJobsSeq(jobs: seq<Job>)
{
    forall job :: job in jobs ==> validJob(job)
}

predicate  differentJobs(j1: Job, j2: Job)
requires validJob(j1) && validJob(j2)
{
    j1.jobStart != j2.jobStart || j1.jobEnd != j2.jobEnd
}

predicate distinctJobsSeq(s: seq<Job>)
requires validJobsSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> differentJobs(s[i], s[j])
}


predicate overlappingJobs(j1:Job, j2:Job)
requires validJob(j1)
requires validJob(j2)
{
    j1.jobEnd > j2.jobStart &&  j2.jobEnd > j1.jobStart //j1.jobEnd <= j2.jobStart || j2.jobEnd <= j1.jobStart
    //primul job se termina inainte ca al 2-lea sa inceapa (j1, j2), si primul job incepe inainte ca al 2-lea sa se termine (j2, j1)
    //ele fiind deja ordonate dupa timpul de finish 
}

predicate startsBeforeEnding(j1:Job, j2:Job)
requires validJob(j1)
requires validJob(j2)
{
    j1.jobEnd > j2.jobStart
}

// predicate disjointJobs(j1:Job, j2:Job)
// requires validJob(j1)
// requires validJob(j2)
// {
//     differentJobs(j1, j2) && !overlappingJobs(j1, j2)
// }

predicate sortedByActEnd(s: seq<Job>)
    requires validJobsSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> JobComparator(s[i], s[j])
}


//intrebarea 1 : Cum as putea scrie ensures? REZOLVAT 
function SolutionProfit(solution: seq<int>, jobs: seq<Job>, index: int): int
requires |solution| == |jobs|
requires 0 <= index <= |solution|
requires 0 <= index <= |jobs|
requires 0 <= |jobs|
requires 0 <= |solution|
decreases |solution| - index 
decreases |jobs| - index 
ensures SolutionProfit(solution, jobs, index ) == if index == |solution| then 0 else solution[index] * jobs[index].profit + SolutionProfit(solution, jobs, index + 1)
{   

    if index == |solution| then 0 else solution[index] * jobs[index].profit + SolutionProfit(solution, jobs, index + 1)
}


function PartialSolutionProfit(solution: seq<int>, jobs: seq<Job>, index: int, firstPosition: int): int
//firstPosition este prima pozitie din jobs, care poate varia de la 0 <= firstPosition < |jobs|
//index este initial 0 si ajunge la lungimea |solution| pt a parcurge toate valorile din solution
requires 0 <= index <= |solution|
requires 0 <= |solution| <= |jobs|
requires 0 <= |solution|
requires 0 <= firstPosition <= |jobs| - index
// requires |jobs| - firstPosition > 0             
requires 0 <= firstPosition <= |jobs| //daca pun <= |jobs| nu mai trebuie |jobs| >= 1 la PartialSolutionProfit
requires 0 <= firstPosition + index <= |jobs|
decreases |solution| - index 
decreases |jobs| - index
ensures PartialSolutionProfit(solution, jobs, index, firstPosition) == if index == |solution| || (firstPosition + index == |jobs|) then 0 else solution[index] * jobs[firstPosition + index].profit + PartialSolutionProfit(solution, jobs, index + 1,firstPosition)
//ensures forall index :: 0 <= index < |solution| ==> PartialSolutionProfit(solution, jobs, index, firstPosition) == if index == |solution| || (firstPosition + index == |jobs| )  then 0 else solution[index] * jobs[firstPosition + index].profit + PartialSolutionProfit(solution, jobs, index + 1, firstPosition);

{   

    if index == |solution| || (firstPosition + index == |jobs| )  then 0 else solution[index] * jobs[firstPosition + index].profit + PartialSolutionProfit(solution, jobs, index + 1, firstPosition)
}

function PartialSolutionPrefixProfit(solution: seq<int>, jobs: seq<Job>, index: int): int
requires 0 <= index <= |solution|
requires 0 <= |solution| <= |jobs|
requires 0 <= |solution|
decreases |solution| - index 
decreases |jobs| - index
ensures PartialSolutionPrefixProfit(solution, jobs, index) == if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionPrefixProfit(solution, jobs, index + 1)
{   

    if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionPrefixProfit(solution, jobs, index + 1)
}

function PartialSolutionPrefixProfit2(solution: seq<int>, jobs: seq<Job>, index1: int, index2: int): int
requires 0 <= index1 <= |solution|
requires 0 <= index2 <= |jobs|
requires 0 <= index2 <= |jobs|
requires 0 <= |solution| <= |jobs|
requires 0 <= |solution|
decreases |solution| - index1
decreases |jobs| - index2
ensures PartialSolutionPrefixProfit2(solution, jobs, index1, index2) == if index1 == |solution| || index2 == |jobs| || solution == [] then 0 else solution[index1] * jobs[index2].profit + PartialSolutionPrefixProfit2(solution, jobs, index1 + 1, index2 + 1)
{   

    if index1 == |solution| || index2 == |jobs| || solution == [] then 0 else solution[index1] * jobs[index2].profit + PartialSolutionPrefixProfit2(solution, jobs, index1 + 1, index2 + 1)
}

// function PartialSolutionPrefixProfitStartFinishPos(solution: seq<int>, jobs: seq<Job>, startPos: int, endPos: int): int
// requires 0 <= startPos <= |solution|
// requires 0 <= startPos <= |jobs|
// requires startPos <= endPos
// requires 0 <= endPos <= |solution|
// requires 0 <= endPos <= |jobs|
// requires 0 <= |solution| <= |jobs|
// requires 0 <= |solution|
// decreases |solution| - startPos
// decreases |jobs| - startPos
// ensures PartialSolutionPrefixProfitStartFinishPos(solution, jobs, startPos, endPos) == if startPos == endPos || |solution| == 0 || startPos == |solution| then 0 else solution[startPos] * jobs[startPos].profit + PartialSolutionPrefixProfitStartFinishPos(solution, jobs, startPos + 1, endPos)
// {   

//     if startPos == endPos ||  |solution| == 0 || startPos == |solution| then 0 else solution[startPos] * jobs[startPos].profit + PartialSolutionPrefixProfitStartFinishPos(solution, jobs, startPos + 1, endPos)
// }

predicate hasNoOverlappingJobs(partialSol: seq<int>, jobs: seq<Job>)
requires validJobsSeq(jobs)
{
   |partialSol| <= |jobs|  && forall i, j :: 0 <= i < j < |partialSol| ==> (partialSol[i] == 1 && partialSol[j] == 1) ==> !overlappingJobs(jobs[i], jobs[j]) 
    //!overlappingJobs asigura si ca job-uri sunt diferite 
}

predicate hasNoOverlappingJobs2(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)//schimb nume 
requires validJobsSeq(jobs)
requires 0 <= j <= i < |jobs|
requires i - j + 1 == |partialSol|
{
    |partialSol| <= |jobs|  && forall x, y :: 0 <= x < y < |partialSol| ==>
        (partialSol[x] == 1 && partialSol[y] == 1) ==> !overlappingJobs(jobs[j + x], jobs[j + y]) 
}

predicate areOrderedByEnd(partialSol: seq<int>, jobs: seq<Job>)
requires validJobsSeq(jobs)
{
   |partialSol| <= |jobs|  && forall i, j :: 0 <= i < j < |partialSol| ==>
        (partialSol[i] == 1 && partialSol[j] == 1) ==> JobComparator(jobs[i], jobs[j]) 
}

predicate areOrderedByEnd2(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
requires validJobsSeq(jobs)
requires 0 <= j <= i < |jobs|
requires i - j + 1 == |partialSol|
{
    |partialSol| <= |jobs|  && forall x, y :: 0 <= x < y < |partialSol| ==>
        (partialSol[x] == 1 && partialSol[y] == 1) ==> JobComparator(jobs[j + x], jobs[j + y]) 
}


lemma Add2NotOverlappingSeq0(seq1: seq<int>, jobs: seq<Job>)
requires validJobsSeq(jobs)
requires |seq1| < |jobs| 
requires hasNoOverlappingJobs(seq1, jobs)
requires areOrderedByEnd(seq1, jobs)
ensures hasNoOverlappingJobs(seq1 + [0], jobs)
{

}

//demonstram ca functia profit este asociativa prin inductie
lemma AssociativityOfProfitFunc(partialSolPrefix : seq<int>, jobs: seq<Job>, val: int, index: int)
requires 1 <= |jobs|
requires validJobsSeq(jobs)
requires 0 <= index <= |partialSolPrefix|
requires 0 <= val <= 1
// requires 1 <= |jobs| - |partialSolPrefix| <= |jobs| 
requires 0 <= |partialSolPrefix| < |jobs| //pentru a ne asiguram ca nu depasim nr de job-uri
decreases |partialSolPrefix| - index 
ensures PartialSolutionPrefixProfit(partialSolPrefix, jobs, index) + val * jobs[|partialSolPrefix|].profit == 
 PartialSolutionPrefixProfit(partialSolPrefix + [val], jobs, index)
{
    //inductie prin recursivitate
  if |partialSolPrefix| == index { //pentru ultima valoare se demonstreaza

  }
  else
  {
    AssociativityOfProfitFunc(partialSolPrefix , jobs, val, index + 1);
  }
}


predicate isPartialSolution(partialSol: seq<int>, jobs: seq<Job>, length: int)
requires validJobsSeq(jobs)
{   //job-urile din solutia partiala nu trebuie sa se suprapuna 
    |partialSol| == length &&
    forall i :: 0 <= i <= |partialSol| - 1 ==> (0 <= partialSol[i] <= 1) && hasNoOverlappingJobs(partialSol, jobs)
}


predicate ValidPartialSolutions(allSol:seq<seq<int>>, jobs: seq<Job>,  index: int)
requires validJobsSeq(jobs)
{   
    |allSol| == index && forall i : int :: 0 <= i < index ==> isPartialSolution(allSol[i], jobs, i + 1) //pana la i + 1 inseamna pana la 2 -> 0 1 

}


ghost predicate isOptimalPartialSolution(partialSol: seq<int>, jobs: seq<Job>, length: int)
requires validJobsSeq(jobs) 
requires |jobs| >= 1
requires length == |partialSol|
requires 1 <= |partialSol| <= |jobs|
{ 
    isPartialSolution(partialSol, jobs, length) && 
    forall otherSol :: isPartialSolution(otherSol, jobs, length) ==> HasLessProfit(otherSol, jobs, PartialSolutionPrefixProfit(partialSol, jobs, 0), 0)
}

predicate HasProfit(partialSol: seq<int>, jobs: seq <Job>, position : int , profit: int )
requires validJobsSeq(jobs) 
requires |jobs| >= 1
requires |partialSol| <= |jobs|
requires 0 <= position < |partialSol|
{
    PartialSolutionPrefixProfit(partialSol, jobs, position) ==  profit
}

ghost predicate isOptimalPartialSolutionDP(partialSol: seq<int>, jobs: seq<Job>, length : int, dp:int)
requires validJobsSeq(jobs) 
requires 1 <= |partialSol| 
requires 1 <= |jobs| 
requires 1 <= length <= |jobs|
{ 
    |partialSol| == length && isOptimalPartialSolution(partialSol, jobs, length) && HasProfit(partialSol, jobs, 0,  dp)
}

ghost predicate OptimalPartialSolutions(allSol: seq<seq<int>>, jobs: seq<Job>, dp:seq<int>, index: int)
requires validJobsSeq(jobs)
requires |allSol| == index
requires index <= |jobs|
requires |dp| == index 
{
     forall i : int :: 0 <= i < index ==> |allSol[i]| == i + 1  && isOptimalPartialSolutionDP(allSol[i], jobs, i + 1, dp[i])
}

predicate isSolution(solution: seq<int>, jobs: seq <Job>) //sa primeasca si datele de intrare (problema) , solutie pt porblema, not overlap
requires validJobsSeq(jobs)
{ 
    isPartialSolution(solution, jobs, |jobs|)
}


ghost predicate isOptimalSolution(solution: seq<int>, jobs: seq<Job>)
requires validJobsSeq(jobs)
requires |jobs| >= 1
requires |solution| == |jobs|
{ 
    isSolution(solution, jobs) && 
    forall otherSol :: isSolution(otherSol, jobs) ==>  PartialSolutionPrefixProfit(solution, jobs, 0) >=  PartialSolutionPrefixProfit(otherSol, jobs, 0)
}

predicate isOptimalSolutionDP(solution: seq<int>, jobs: seq<Job>, dp: int)
requires validJobsSeq(jobs) 
requires |solution| == |jobs|
{ 
    isSolution(solution, jobs) && SolutionProfit(solution, jobs, 0) == dp
}

predicate containsOnlyZeros(partialSol: seq<int>)
{
    forall x :: 0 <= x < |partialSol| ==> partialSol[x] == 0
}

predicate partialSolutionWithJobI(partialSol: seq<int>, jobs: seq<Job>,  i: int)
requires validJobsSeq(jobs)
requires 0 <= i < |partialSol|
{
    isPartialSolution(partialSol, jobs, |partialSol|) && partialSol[i] == 1
}

predicate partialSolutionWithoutJobI(partialSol: seq<int>, jobs: seq<Job>,  i: int)
requires validJobsSeq(jobs)
requires 0 <= i < |partialSol|
{
    isPartialSolution(partialSol, jobs, |partialSol|) && partialSol[i] == 0
}

predicate HasLessProfit(partialSol: seq<int>, jobs: seq<Job>,  maxProfit: int, position: int)
requires validJobsSeq(jobs)
requires 0 <= position < |partialSol|
requires |partialSol| <= |jobs|
{
    PartialSolutionPrefixProfit(partialSol, jobs, position) <= maxProfit
}

predicate HasMoreProfit(partialSol: seq<int>, jobs: seq<Job>,  maxProfit: int, position: int)
requires validJobsSeq(jobs)
requires 0 <= position < |partialSol|
requires |partialSol| <= |jobs|
{
    PartialSolutionPrefixProfit(partialSol, jobs, position) > maxProfit
}


lemma AddSplittedPartialSol(partialSol: seq<int>, jobs:seq<Job>, index: int)
requires validJobsSeq(jobs)
requires 1 <= |jobs|
requires |partialSol| <= |jobs|
requires 0 <= index <= |partialSol| //index-ul ppoate fi ultima pozitie //functie profit cu 2 index apelata doar cu partialSol complet 
ensures PartialSolutionPrefixProfit(partialSol[..index], jobs, 0) + PartialSolutionPrefixProfit(partialSol, jobs, index) == PartialSolutionPrefixProfit(partialSol, jobs, 0)  
decreases |partialSol| - index 
{
    if index == |partialSol|
    {   //index este ultima valoare din partialSol
        assert PartialSolutionPrefixProfit(partialSol, jobs, index) == 0;
        assert partialSol[..index] == partialSol;
        assert PartialSolutionPrefixProfit(partialSol[..index], jobs, 0) + 0 == PartialSolutionPrefixProfit(partialSol, jobs, 0);
        assert PartialSolutionPrefixProfit(partialSol[..index], jobs, 0) + PartialSolutionPrefixProfit(partialSol, jobs, index) == PartialSolutionPrefixProfit(partialSol, jobs, 0);
    }
    else{
        var profit := PartialSolutionPrefixProfit(partialSol, jobs, 0);
        var profit1 := PartialSolutionPrefixProfit(partialSol[..index], jobs, 0);
        var profit2 := PartialSolutionPrefixProfit(partialSol, jobs, index);
        assert partialSol[..index+1][..index] == partialSol[..index];
        assert partialSol[..index] + partialSol[index..] == partialSol;
        //AddSplittedPartialSol(partialSol, jobs, index + 1); //apelam mereu inainte pentru a demonstra
        //assert PartialSolutionPrefixProfit(partialSol[..index], jobs, 0) + PartialSolutionPrefixProfit(partialSol, jobs, index) == PartialSolutionPrefixProfit(partialSol, jobs, 0);
        //assert partialSol[..index] + partialSol[index..] == partialSol;
        assume profit1 + profit2 == profit; //help
        

    }

    
} 

function PartialSolutionPrefixProfitStartFinishPos(solution: seq<int>, jobs: seq<Job>, startPos: int, endPos: int): int
requires 0 <= startPos <= |solution|
requires 0 <= startPos <= |jobs|
requires startPos <= endPos
requires 0 <= endPos <= |solution|
requires 0 <= endPos <= |jobs|
requires 0 <= |solution| <= |jobs|
requires 0 <= |solution|
decreases |solution| - startPos
decreases |jobs| - startPos
ensures PartialSolutionPrefixProfitStartFinishPos(solution, jobs, startPos, endPos) == if startPos == endPos then 0 else solution[startPos] * jobs[startPos].profit + PartialSolutionPrefixProfitStartFinishPos(solution, jobs, startPos + 1, endPos)
{   

    if startPos == endPos then 0 else solution[startPos] * jobs[startPos].profit + PartialSolutionPrefixProfitStartFinishPos(solution, jobs, startPos + 1, endPos)
}

// + o lemma in care demonstres PartialSolutionPrefix(partialSol, jobs, j + 1) ==  PartialSolutionPrefixProfitStartFinishPos(solution, jobs, j + 1, |solution|) //scoatem jobs[i].profits
//PartialSolutionPrefix(partialSol, jobs, 0) ==  PartialSolutionPrefixProfitStartFinishPos(solution, jobs, 0, |solution|) + lemma
//PartialSolutionPrefix(partialSol[..j+1], jobs, 0) ==  PartialSolutionPrefixProfitStartFinishPos(solution, jobs, 0, j + 1) + lemma 
lemma A(partialSolution: seq<int>, jobs: seq<Job>, startPos: int)
requires startPos == 0 
requires 0 < |partialSolution| <= |jobs|
ensures PartialSolutionPrefixProfitStartFinishPos(partialSolution, jobs, startPos, |partialSolution|) == PartialSolutionPrefixProfit(partialSolution, jobs, startPos)
decreases |partialSolution| - startPos
{
    
    if startPos == |partialSolution|
    {

    }
    else
    {
        C(partialSolution, jobs, startPos + 1);
    }
}


lemma B(partialSolution: seq<int>, jobs: seq<Job>, startPos: int, index: int) //PartialSolutionPrefiProfit(partialSol[..j+1], jobs, 0)
requires 0 <= startPos <= index 
requires 0 <= index <= |partialSolution|
requires 0 < |partialSolution| <= |jobs|
ensures  PartialSolutionPrefixProfitStartFinishPos(partialSolution, jobs, startPos, index) == PartialSolutionPrefixProfit(partialSolution[..index], jobs, startPos)
decreases index - startPos
{   
    if startPos == index{
        assert PartialSolutionPrefixProfitStartFinishPos(partialSolution, jobs, startPos, index) == 0;
    }
    else{
        B(partialSolution, jobs, startPos + 1, index);
    }
}

lemma C(partialSolution: seq<int>, jobs: seq<Job>, index: int) //PartialSolutionPrefixProfit(partialSol, jobs, j + 1)
requires 0 <= index <= |partialSolution|
requires 0 < |partialSolution| <= |jobs|
ensures  PartialSolutionPrefixProfitStartFinishPos(partialSolution, jobs, index, |partialSolution|) ==
 PartialSolutionPrefixProfit(partialSolution, jobs, index)
decreases |partialSolution| - index
{
    if index == |partialSolution|{
        assert PartialSolutionPrefixProfitStartFinishPos(partialSolution, jobs, index, |partialSolution|) == 0;
        assert PartialSolutionPrefixProfit(partialSolution, jobs, index) == 0;
    }
    else{
        C(partialSolution, jobs, index + 1);
    }

}

//help //here
lemma SplitSequenceProfitEquality(partialSol: seq<int>, jobs: seq<Job>, startPos: int, index: int)
requires 0 <= index < |partialSol|  
requires 0 <= startPos < index
requires 0 <= |partialSol| <= |jobs|
ensures PartialSolutionPrefixProfitStartFinishPos(partialSol, jobs, startPos, |partialSol|) == PartialSolutionPrefixProfitStartFinishPos(partialSol, jobs, startPos, index) + PartialSolutionPrefixProfitStartFinishPos(partialSol, jobs, index, |partialSol|)
decreases  index - startPos
{   
    //help
    // if startPos == index {
    //     assert PartialSolutionPrefixProfitStartFinishPos(solution, jobs, startPos, index) == 0;
    // } else {
    //     // Recursive case
    //     var leftProfit := PartialSolutionPrefixProfitStartFinishPos(solution, jobs, startPos, index);
    //     var rightProfit := PartialSolutionPrefixProfitStartFinishPos(solution, jobs, index, |solution|);
    //     var totalProfit := PartialSolutionPrefixProfit2(solution, jobs, startPos, |solution|);
    //     //assert solution[..st][..index] == solution[..index];
    //     //SplitSequenceProfitEquality(solution, jobs, startPos + 1, index);
    //     assert solution[..index] + solution[index..] == solution;
    //     //assume totalProfit == leftProfit + rightProfit;
    // }
}


lemma ComputeProfitWhenOnly0BetweenJI(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
requires validJobsSeq(jobs)
requires 0 < i < |partialSol|
requires |partialSol| == i + 1
requires 0 <= j < i < |partialSol|
requires |partialSol| <= |jobs|
requires isPartialSolution(partialSol, jobs, |partialSol|)
requires partialSolutionWithJobI(partialSol, jobs, i)
requires forall k :: j < k < i ==> partialSol[k] == 0 
ensures PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == jobs[i].profit 
decreases i - j
{   
    if j == i - 1 
    {
        assert PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == jobs[i].profit;
    }
    else 
    {
        ComputeProfitWhenOnly0BetweenJI(partialSol, jobs, i, j + 1);
    }
    assert partialSol[i] == 1;
    assert PartialSolutionPrefixProfit(partialSol, jobs, i) == jobs[i].profit;
    assert forall k :: j < k < i ==> partialSol[k] == 0;
    assert PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == jobs[i].profit;
    
}

lemma OtherSolHasLessProfitThenMaxProfit2(partialSol: seq<int>, jobs : seq<Job>, i: int, j : int, max_profit : int, allSol : seq<seq<int>>, dp: seq<int>)
requires validJobsSeq(jobs)
requires 0 < i < |jobs|
requires 0 <= j < i
requires |dp| == i  //nr de profituri optime pentru solutiile partiale optime din fata lui este egal i 
requires PositiveProfitsDP(dp)
requires |allSol| == i //nr de solutii partiale optime cu job-urile de pe pozitiile 0, ..., i-1 este i 
requires OptimalPartialSolutions(allSol, jobs, dp, i)
requires isOptimalPartialSolution(allSol[j], jobs, j + 1)
requires isOptimalPartialSolution(allSol[j], jobs, j + 1) //stim ca allSol[j] este solutia partiala optima pana la pozitia j si are profitul pozotiv dp[j]
requires max_profit == dp[j] + jobs[i].profit //profitul pentru allSol[j] si profitul pentru job-ul i 
requires forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i])
requires !overlappingJobs(jobs[j], jobs[i])
requires forall k :: 0 <= k <= j && allSol[j][k] != 0 ==> !overlappingJobs(jobs[k], jobs[i]) //allSol[1] are 2 elemente pe poz 0 si 1 
requires |partialSol| == i + 1
requires partialSolutionWithJobI(partialSol, jobs, i)
requires PartialSolutionPrefixProfit(partialSol, jobs, i) == jobs[i].profit;
requires isPartialSolution(partialSol, jobs, i + 1)
requires forall k :: j < k < i ==> partialSol[k] == 0
ensures HasLessProfit(partialSol, jobs, max_profit, 0)
{
    
    var k : int := i - 1; // pe pozitia i se afla job-ul i 
    assert |partialSol| == i + 1;
    assert j <= k < i;
    assert !exists k' :: k < k' < i; 
    assert forall k' :: k < k' < i ==> partialSol[k'] == 0; //asta vreau sa demonstrez ==> ca am doar 0 -rouri pe pozitiile i - 1 ...0 
    assert PartialSolutionPrefixProfit(partialSol, jobs, k + 1) == jobs[i].profit;
    //assume false;

    ComputeProfitWhenOnly0BetweenJI(partialSol, jobs, i, j);
    assert PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == jobs[i].profit;
    //presupunem contrariul 
    if !HasLessProfit(partialSol, jobs, max_profit, 0) //presupunem ca ar exista o solutie partiala care indeplineste conditiile si care 
    //sa aiba profitul mai mare decat max_profit
    {   
        //assume false;
        var profit' := PartialSolutionPrefixProfit(partialSol, jobs, 0);
        assert max_profit == dp[j] + jobs[i].profit;
        assert HasMoreProfit(partialSol, jobs, max_profit, 0);
        assert !HasLessProfit(partialSol, jobs, max_profit, 0);
        assert partialSol[..j+1] + partialSol[j+1..] == partialSol; 
        //apelam lemmele ajutatoare
        SplitSequenceProfitEquality(partialSol, jobs, 0, j + 1);
        A(partialSol, jobs, 0);  //here
        B(partialSol, jobs, 0, j + 1);
        C(partialSol, jobs, j + 1);
        //AddSplittedPartialSol(partialSol, jobs, j + 1);
        assert PartialSolutionPrefixProfit(partialSol[..j + 1], jobs, 0) + PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == PartialSolutionPrefixProfit(partialSol, jobs, 0);
        assert PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == jobs[i].profit;
        var partialSol' :seq<int> := partialSol[..j+1];
        assert isPartialSolution(partialSol', jobs, j+1);
        var profit := PartialSolutionPrefixProfit(partialSol', jobs, 0);
        assert |partialSol'| == j + 1;
        assert partialSol' + partialSol[j+1..] == partialSol;
        assert profit + jobs[i].profit == profit';
        assert profit + jobs[i].profit > max_profit;
        assert profit > max_profit - jobs[i].profit;
        assert profit > dp[j];
        assert dp[j] == PartialSolutionPrefixProfit(allSol[j], jobs, 0);
        assert isOptimalPartialSolution(allSol[j], jobs, j + 1);
        assert forall otherSol:: isPartialSolution(otherSol, jobs, j + 1) ==> HasLessProfit(otherSol, jobs, dp[j], 0);
        assert !isOptimalPartialSolution(allSol[j], jobs, j + 1);
        assert false;
    }

    assert HasLessProfit(partialSol, jobs, max_profit, 0);
    
}

lemma OnlY0WhenOverlapJobs(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
requires validJobsSeq(jobs)
requires |partialSol| <= |jobs|
requires isPartialSolution(partialSol, jobs, i + 1)
requires 0 <= j < i < |partialSol|
requires partialSolutionWithJobI(partialSol, jobs, i)
requires forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i])
requires hasNoOverlappingJobs(partialSol, jobs);
requires !overlappingJobs(jobs[j], jobs[i])
ensures forall k :: j < k < i ==> partialSol[k] == 0
{   
    assert isPartialSolution(partialSol, jobs, i + 1);
    assert hasNoOverlappingJobs(partialSol, jobs);
    assert forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]);
    forall k | j < k < i < |partialSol|
    ensures partialSol[k] == 0 
    {   
        if partialSol[k] == 1
        {
            assert overlappingJobs(jobs[k], jobs[i]);
            //assert !hasNoOverlappingJobs(partialSol, jobs);
            assert !isPartialSolution(partialSol, jobs, i + 1);
            assert false;
        }
    
    }
}


lemma AddNotOverlappingSeq(a: seq<int>, jobs: seq<Job>, i: int, j: int)
requires validJobsSeq(jobs)
requires sortedByActEnd(jobs) //toate job-urile sunt ordonate dupa timpul de sf 
requires distinctJobsSeq(jobs)
requires |a| < |jobs|
requires |a| == j + 1; //allSol[j]
requires 0 <= j < i < |jobs| 
requires jobs[j].jobEnd <= jobs[i].jobStart; // j nu se suprapune cu i 
requires !overlappingJobs(jobs[j], jobs[i]) //jobs[j].actEnd <= jobs[i].actStart
requires isPartialSolution(a, jobs, |a|) //allSol[j] este solutie partiala 
requires hasNoOverlappingJobs(a, jobs)
ensures forall k :: 0 <= k < |a| ==> a[k] == 1 ==> !overlappingJobs(jobs[k], jobs[i])
{   
    assert forall k, k' :: 0 <= k < k' <= j ==> jobs[k].jobEnd <= jobs[k'].jobEnd; //sunt sortate dupa timpul de sf 
    assert forall k :: 0 <= k <= j ==> validJob(jobs[k]);
    assert forall k :: 0 <= k <= j ==> jobs[k].jobStart <= jobs[k].jobEnd; //sunt sortate dupa timpul de sf 
    assert !overlappingJobs(jobs[j], jobs[i]);
    assert validJob(jobs[j]); 
    assert jobs[j].jobStart < jobs[j].jobEnd;
    assert jobs[j].jobEnd <= jobs[i].jobStart;
    assert jobs[j].jobStart < jobs[i].jobStart;
    assert forall k :: 0 <= k <= j ==> jobs[k].jobEnd <= jobs[i].jobStart; //sunt sortate dupa timpul de sf 
    assert forall k :: 0 <= k <= j ==> a[k] == 1 ==> !overlappingJobs(jobs[k], jobs[i]); //sunt sortate dupa timpul de sf 
    //assert hasNoOverlappingJobs(a, jobs);
}

lemma NotOverlappingJobsSeq(a: seq<int>, jobs: seq<Job>, i: int, j: int)
requires validJobsSeq(jobs)
requires sortedByActEnd(jobs)
requires distinctJobsSeq(jobs) //toate job-urile sunt ordonate dupa timpul de sf 
requires |a| <= |jobs|
requires |a| == i + 1;
requires 0 <= j < i < |jobs|
requires a[i] == 1 //pe pozitia i avem 1 
requires !overlappingJobs(jobs[j], jobs[i]) //jobs[j].actEnd <= jobs[i].actStart
requires isPartialSolution(a[..j+1], jobs, j + 1) //allSol[j]
requires hasNoOverlappingJobs(a[..j+1], jobs) //allSol[j] nu contine job-uri care se suprapun
requires forall k :: 0 <= k < |a[..j + 1]| ==> a[k] == 1 ==> !overlappingJobs(jobs[k], jobs[i]) //lemma anterioara 
requires forall k :: j + 1 <= k < i ==> a[k] == 0
requires forall k :: j + 1 <= k < i ==> overlappingJobs(jobs[k], jobs[i])
ensures hasNoOverlappingJobs(a, jobs)
ensures forall k :: 0 <= k < i ==> a[k] == 1 ==> !overlappingJobs(jobs[k], jobs[i])
{

}

//gasim un job j care nu se suprapune cu i 
//dp - secventa cu toate profiturile solutiilor partiale optime cu job-uri pana la pozitia 0, 1.., i-1   
//allSol secventa de secvente ce reprezinta solutiile optime de lungime 0, ... i -1, cu job-urile pana la pozitia i 
method  OptimalPartialSolutionWhenNonOverlapJob(jobs: seq <Job>, i: int, dp: seq<int>, allSol :seq<seq<int>>, j : int) returns (maxProfit:int, partialSolution: seq<int>, length: int)
requires 1 <= |jobs|
requires validJobsSeq(jobs)
requires distinctJobsSeq(jobs)
requires sortedByActEnd(jobs)
requires 1 <= i < |jobs|
requires 1 <= |dp| < |jobs|
requires 1 <= |allSol| <= |jobs|
requires |allSol| == i 
requires |dp| == i
requires 0 <= j < i
requires PositiveProfitsDP(dp)
requires OptimalPartialSolutions(allSol, jobs, dp, i)
requires ValidPartialSolutions(allSol, jobs, i)
requires !overlappingJobs(jobs[j], jobs[i]);
requires hasNoOverlappingJobs(allSol[j], jobs); 
// requires forall k :: 0 <= k < |allSol[j]| ==> allSol[j][k] == 1 ==> !overlappingJobs(jobs[k], jobs[j]);
requires jobs[j].jobEnd <= jobs[i].jobStart
requires HasProfit(allSol[j], jobs, 0,  dp[j]);
requires isOptimalPartialSolution(allSol[j], jobs, |allSol[j]|); 
requires forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i])
requires !overlappingJobs(jobs[j], jobs[i]);
ensures isPartialSolution(partialSolution, jobs, i + 1)
ensures maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0)
ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0) 
ensures length == i + 1;
ensures |partialSolution| <= |jobs|
ensures forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolution[i] <= 1;
ensures partialSolutionWithJobI(partialSolution, jobs, i)
{
    var partialSolutionPrefix : seq<int> := [];
    var max_profit : int := 0 ;
    length := 0;
    partialSolutionPrefix := allSol[j];
    length := length + |allSol[j]|; 
    assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1; //toate elementele sunt 0 sau 1 
    assert hasNoOverlappingJobs(partialSolutionPrefix, jobs); //nu are job-uri care se suprapun pentru ca allSol[j] este solutie partiala optima
    max_profit := max_profit + dp[j]; //adaug profitul pt solutia partiala optima (cu job-uri pana la pozitia j)
    var nr_of_zeros := i - |allSol[j]|; // nr de elemente dintre i si j 
    assert |allSol[j]| == j + 1;
    assert length + nr_of_zeros < |jobs|;
    assert nr_of_zeros + |allSol[j]| == i ;  
    while nr_of_zeros > 0 
        decreases nr_of_zeros
        invariant 0 <= nr_of_zeros <= i - |allSol[j]| //setam limitele pentru nr_of_zeros
        decreases i - length 
        invariant |allSol[j]| <= length <= i
        invariant |partialSolutionPrefix| == length
        invariant forall k :: 0 <= k <= length - 1 ==> 0 <= partialSolutionPrefix[k] <= 1
        invariant length + nr_of_zeros < |jobs|;
        invariant length + nr_of_zeros <= i;
        invariant length < |jobs|;
        invariant length == i - nr_of_zeros
        invariant nr_of_zeros == 0 ==> length == i 
        invariant length == i ==> nr_of_zeros == 0 
        invariant hasNoOverlappingJobs(partialSolutionPrefix, jobs)
        invariant forall k :: j < k < |partialSolutionPrefix| ==> partialSolutionPrefix[k] == 0
        invariant max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0)
        invariant |allSol[j]| <= |partialSolutionPrefix| < |jobs| 
            {   
                //assume false;
                AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 0, 0); //demonstram ca daca adaugam 0 profitul "ramane acelasi" 0 * jobs[..]
                assert max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0);
                partialSolutionPrefix :=  partialSolutionPrefix + [0]; //se adauga de nr_of_zeros ori 
                assert length + nr_of_zeros < |jobs|;
                length := length + 1;
                nr_of_zeros := nr_of_zeros - 1;
                assert max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0); 
            }
    assert nr_of_zeros == 0;
    assert length == i; //de demonstrat 
    assert |partialSolutionPrefix| == i ;

    assert forall k :: j < k < i ==> partialSolutionPrefix[k] == 0;
    assert forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]); //stim ca toate job-urile strict mai mari decat j se suprapun cu i 
    
    //allSol[j] contine job-uri care nu se suprapun, j nu se suprapune cu i 
    // assert forall k :: j + 1 <= k < i ==> partialSolutionPrefix[k] == 0;
    // assert forall k :: j + 1 <= k < i ==> overlappingJobs(jobs[k], jobs[i]);
    
    //assume false;
    //assert forall k :: 0 <= k < |allSol[j]| ==> allSol[j][k] == 1 ==> !overlappingJobs(jobs[k], jobs[i]);

    assert |partialSolutionPrefix| == length;
    assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
    assert hasNoOverlappingJobs(partialSolutionPrefix, jobs);

    AddNotOverlappingSeq(allSol[j], jobs, i, j); //demonstram ca toate job-urile prezente in allSol[j] nu se suprapun cu i
    NotOverlappingJobsSeq(partialSolutionPrefix + [1], jobs, i, j); //demonstram ca partialSolutionPrefix nu contine job-uri care sa se suprapuna
    assert hasNoOverlappingJobs(partialSolutionPrefix + [1], jobs);

    AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 1, 0); //apelam inainte sa adaugam 1 
    partialSolutionPrefix := partialSolutionPrefix + [1]; //includem si job-ul i (solutia partiala ce contine job-ul i)
    length := length + 1;

    //solutie partiala 
    assert |partialSolutionPrefix| == length;
    assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
    assert hasNoOverlappingJobs(partialSolutionPrefix, jobs);
    //assume false; //help

    //assume false;
    max_profit := max_profit + jobs[i].profit;
    assert max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0);
    forall partialSol | |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) 
    ensures HasLessProfit(partialSol, jobs, max_profit, 0) 
     {
       //assume forall k :: j < k < i ==> partialSol[k] == 0;
       OnlY0WhenOverlapJobs(partialSol, jobs, i, j);
       assert forall k :: j < k < i ==> partialSol[k] == 0;
       assert PartialSolutionPrefixProfit(partialSol, jobs, i) == jobs[i].profit;
       OtherSolHasLessProfitThenMaxProfit2(partialSol, jobs, i, j, max_profit, allSol, dp);
       //assume false;
     }

    //assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit, 0) ;
    maxProfit := max_profit;
    partialSolution := partialSolutionPrefix;
}

//lemma ajutor pt functia de mai jos 
lemma OtherSolHasLessProfitThenMaxProfit(jobs : seq<Job>, i: int, j : int, max_profit : int)
requires validJobsSeq(jobs)
requires 0 < i < |jobs|
requires max_profit == jobs[i].profit
requires forall j :: 0 <= j < i ==> overlappingJobs(jobs[j], jobs[i])
ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit, 0)
{
    forall partialSol | |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i)
    ensures HasLessProfit(partialSol, jobs, max_profit, 0) { // <= 
        assert isPartialSolution(partialSol, jobs, i + 1);
        var k := i - 1; // pe pozitia i se afla job-ul i 
        //assert partialSol[k] == 0;
        assert |partialSol| == i + 1;
        assert -1 <= k < i;
        assert !exists k' :: k < k' < i; 
        assert forall k' :: k < k' < i ==> partialSol[k'] == 0; //asta vreau sa demonstrez ==> ca am doar 0 -rouri pe pozitiile i - 1 ...0 
        assert PartialSolutionPrefixProfit(partialSol, jobs, k + 1) == jobs[i].profit;
        //lemma
        while k >= 0 //k > 0 , ajungeam pana la 1 si invariantul era ori k' >= k (imposibil), ori k' > k => ultimele pozitii verificare erau > 1 = 2 (1)
            decreases k
            invariant -1 <= k < i
            invariant forall k' :: k < k' < i ==> partialSol[k'] == 0 //asta vreau sa demonstrez ==> ca am doar 0 -rouri pe pozitiile i - 1 ...0 
            invariant PartialSolutionPrefixProfit(partialSol, jobs, k + 1) == jobs[i].profit //demonstram de la 0 la i pentru toate job-urile 
            {   
                // assume false;
                if partialSol[k] == 1 {
                    
                    //assume false;
                    assert partialSol[i] == 1;
                    
                    assert overlappingJobs(jobs[k], jobs[i]);
                    
                    assert !isPartialSolution(partialSol, jobs, i + 1); //demonstram ca daca ar fi 1 s-ar contrazice cu ipoteza ==> doar 0-uri 
                    // assume false;
                    assert false;

                }
                // else{
                //     assume false;
                //     assert partialSol[k] == 0; //trivial ?? meaning , avem deja in invariant
                // }
                // assume false;
                assert forall k' :: k < k' < i ==> partialSol[k'] == 0;
                assert partialSol[k] == 0;
                assert forall k' :: k <= k' < i ==> partialSol[k'] == 0; //in while demonstrezi pentru k' = k
                k := k - 1;
                assert forall k' :: k < k' < i ==> partialSol[k'] == 0;
                // assume false;
            }
        //assume false;
        assert PartialSolutionPrefixProfit(partialSol, jobs, 0) == jobs[i].profit; //lemma tot 0, profit 0 
    }
}

//DEMONSTRATA doar 0-uri in fata lui i 
method  OptimalPartialSolutionWhenOverlapJob(jobs: seq <Job>, i: int, dp: seq<int>, j : int) returns (maxProfit:int, partialSolution: seq<int>, length: int)
requires validJobsSeq(jobs)
requires distinctJobsSeq(jobs)
requires sortedByActEnd(jobs)
requires 1 <= i < |jobs|
requires 1 <= |dp| < |jobs|
requires |dp| == i
requires j == -1 //de inloc
requires forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i])
ensures isPartialSolution(partialSolution, jobs, i + 1)
ensures maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0)
ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0) 
ensures length == i + 1;
ensures |partialSolution| <= |jobs|
ensures forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolution[i] <= 1;
ensures partialSolutionWithJobI(partialSolution, jobs, i)
{
    // assume false;
    var partialSolutionPrefix : seq<int> := [];
    var max_profit : int := 0 ;
    length := 0;
    assert j == -1;
    //assume false;  
    //cazul in care punem numai zerouri 
    assert forall k :: 0 < k < i ==> overlappingJobs(jobs[k], jobs[i]);
    var nr_of_zeros := i; 
    while nr_of_zeros > 0 
        decreases nr_of_zeros
        decreases i - length
        invariant 0 <= nr_of_zeros <= i
        invariant |partialSolutionPrefix| == length
        invariant forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
        invariant length + nr_of_zeros <= i;
        invariant length < |jobs|;
        invariant length == i - nr_of_zeros
        invariant nr_of_zeros == 0 ==> length == i 
        invariant hasNoOverlappingJobs(partialSolutionPrefix, jobs)
        invariant max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0)
        invariant max_profit == 0
        invariant forall k :: 0 <= k < |partialSolutionPrefix| ==> partialSolutionPrefix[k] == 0
            {   
                AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 0, 0);
                partialSolutionPrefix :=  partialSolutionPrefix + [0];
                length := length + 1;
                nr_of_zeros := nr_of_zeros - 1;
                max_profit := max_profit + 0 ;
            }
    assert length == i;
    assert containsOnlyZeros(partialSolutionPrefix);
    max_profit := max_profit + jobs[i].profit; //contine doar job-ul i 
    assert partialSolutionWithJobI(partialSolutionPrefix + [1], jobs, i);
  
    assert forall k :: 0 <= k < i ==> partialSolutionPrefix[k] == 0; //de reluat definitia 
    assert forall k :: 0 <= k < i ==> overlappingJobs(jobs[k], jobs[i]); //de reluat definitia 
    assert isPartialSolution(partialSolutionPrefix, jobs, i);
    
    OtherSolHasLessProfitThenMaxProfit(jobs, i, j, max_profit);

    assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit, 0) ;
    
    assert |partialSolutionPrefix| == length;
    assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
    assert hasNoOverlappingJobs(partialSolutionPrefix, jobs); //deoarece avem un invariant in care stim ca toate job-urile din fata lui i sunt 0 

    AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 1, 0); //apelata pentru max_profit
    
    partialSolutionPrefix := partialSolutionPrefix + [1]; //includem si job-ul i (solutia partiala ce contine job-ul i)
    assert |partialSolutionPrefix| == i + 1;
    length := length + 1;
    assert max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0);
    assert isPartialSolution(partialSolutionPrefix, jobs, length);

    assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit, 0) ;

    partialSolution := partialSolutionPrefix;
    maxProfit := max_profit;
}

predicate PositiveProfitsDP(dp: seq<int>)
{
    forall i :: 0 <= i < |dp| ==> dp[i] >= 0 
}

//predicat in care ma asigur ca toate profiturile dp sunt strict >= 0 
//inca nedemonstrat max_profit
//functia maxprofit intoarce solutia partiala ce contine job-ul i 
method MaxProfitWithJobI(jobs: seq <Job>, i: int, dp: seq<int>, allSol :seq<seq<int>>) returns (maxProfit:int, partialSolution: seq<int>)
requires validJobsSeq(jobs)
requires 1 <= |jobs|
requires distinctJobsSeq(jobs)
requires sortedByActEnd(jobs)
requires PositiveProfitsDP(dp)
requires 1 <= i < |jobs|
requires 1 <= |dp| < |jobs|
requires 1 <= |allSol| <= |jobs|
requires |allSol| == i 
requires |dp| == i
requires OptimalPartialSolutions(allSol, jobs, dp, i)
requires ValidPartialSolutions(allSol, jobs, i) //cerem ca all sol sa contina doar secvente de 0 si 1 si pentru toate 0 <= j < i allSol[j] == j + 1
ensures isPartialSolution(partialSolution, jobs, i + 1)
ensures maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0)
ensures partialSolutionWithJobI(partialSolution, jobs, i)
ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0) 
{       
       
        var max_profit := 0;
        var partialSolutionPrefix : seq<int> := [];
        var j := i - 1;
        var length := 0;
        //assert  j != -1 ==> max_profit == PartialSolutionProfit(subSol, jobs, 0, j + 1) ;
        while j >= 0 && jobs[j].jobEnd > jobs[i].jobStart //
            invariant - 1 <= j < i
            invariant forall k :: j < k < i ==> jobs[k].jobEnd > jobs[i].jobStart //se suprapun
            invariant forall k :: j < k < i ==> validJob(jobs[k]) 
            invariant forall k :: j < k < i ==> JobComparator(jobs[k], jobs[i]) //din OrderedByEnd
            invariant forall k :: j < k < i ==> jobs[k].jobEnd > jobs[k].jobStart //din ValidJob
            invariant forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]) //stiu doar despre primul job j(ultima val a while-ului) nu se suprapune cu i 
                {   
                    j := j - 1;            
                } 

        assert  j != -1 ==> !overlappingJobs(jobs[j], jobs[i]);
        assert |partialSolutionPrefix| == length;
        assert hasNoOverlappingJobs(partialSolutionPrefix, jobs);

        //assume false;
        if j >= 0 //inseamna ca a gasit un job j cu care nu se suprapune pe o pozitie >= 0 
        {  

            max_profit, partialSolution, length := OptimalPartialSolutionWhenNonOverlapJob(jobs, i, dp, allSol, j);
            //assume false;

        } 
        else
        {   
            //only 0 before i 
            //assume false;
            max_profit, partialSolution, length := OptimalPartialSolutionWhenOverlapJob(jobs, i, dp, j);
            
        }
        assert length == i + 1;
        assert |partialSolution| == length;
        assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolution[i] <= 1;
        assert |partialSolution| <= |jobs|; 
        assert hasNoOverlappingJobs(partialSolution, jobs);

        assert isPartialSolution(partialSolution, jobs, length);
        
        assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit, 0) ;
        //assume false;
        maxProfit := max_profit;
        assert maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0); 
}


lemma NotAddingAJobKeepsSameProfit(partialSol: seq<int>, jobs: seq <Job>, index: int)
requires validJobsSeq(jobs)
requires |partialSol| < |jobs|
requires 0 <= index <= |partialSol|
decreases |partialSol| - index 
ensures PartialSolutionPrefixProfit(partialSol, jobs, index) == PartialSolutionPrefixProfit(partialSol + [0], jobs, index)
{
 if |partialSol| == index {
    assert PartialSolutionPrefixProfit(partialSol, jobs, index) == PartialSolutionPrefixProfit(partialSol + [0], jobs, index);

 }
 else
 {
    NotAddingAJobKeepsSameProfit(partialSol, jobs, index + 1);
 }

}

lemma ifOptimalPartialSolutions(allSol: seq<seq<int>>, jobs:seq<Job>, dp : seq<int>, i: int)
requires validJobsSeq(jobs)
requires 1 <= |jobs|
requires |allSol| == i
requires |dp| == i 
requires 1 <= i < |jobs|
requires OptimalPartialSolutions(allSol, jobs, dp, i)
ensures HasProfit(allSol[i - 1], jobs, 0,  dp[i - 1])
{

}

lemma SubSeqOfPartialIsAlsoPartial(partialSol: seq<int>, jobs: seq<Job>, length: int)
requires length + 1 == |partialSol|
requires 0 <= length < |jobs|
requires validJobsSeq(jobs)
requires isPartialSolution(partialSol, jobs, length + 1)
ensures isPartialSolution(partialSol[..length], jobs, length)
{

}

lemma optimalPartialSolutionWithJobI(i: int, jobs: seq<Job>, maxProfit: int, allSol: seq<seq<int>>, dp: seq<int>)
requires validJobsSeq(jobs)
requires |allSol| == i 
requires |dp| == i
requires 1 <= i < |jobs|
requires OptimalPartialSolutions(allSol, jobs, dp, i)
requires dp[i - 1] < maxProfit
requires forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i //stim din invariant 
requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
ensures forall partialSol :: |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|) ==> HasLessProfit(partialSol, jobs, maxProfit, 0);
{
    forall partialSol | |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|)
    ensures HasLessProfit(partialSol, jobs, maxProfit, 0);
    {   
        if partialSol[i] == 1
        {   
            assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0);
            //assume false;
            //demonstrat din functia MaxProfitWithJobI
        }
        else{
                //daca nu adaug un job profitul ramane <= dp[i-1] (invariant sulutie partiala optima), care in aceasta ramura a if-ului este <= max_profit 
                // ==> tranzitivitate ==> profitul curent <= dp[i] (= max_profit)
                //nu se demonstreaza 
                //daca nu punem job-ul i => punem 0 si profitul este <= dp[i-1] (optim) (pasul anterior), dp[i - 1] < max_profit => tranzitivitate <= max_profit
                NotAddingAJobKeepsSameProfit(partialSol[..i], jobs, 0);
                assert partialSol[..i] + [0] == partialSol;
                assert PartialSolutionPrefixProfit(partialSol[..i], jobs, 0) == PartialSolutionPrefixProfit(partialSol, jobs, 0);
                assert OptimalPartialSolutions(allSol, jobs, dp, i);
                assert isOptimalPartialSolution(allSol[i - 1], jobs, |allSol[i - 1]|);
                assert PartialSolutionPrefixProfit(allSol[i - 1], jobs, 0) == dp[i - 1];
                assert HasProfit(allSol[i - 1], jobs, 0,  dp[i - 1]); 
                SubSeqOfPartialIsAlsoPartial(partialSol, jobs, i);
                assert isPartialSolution(partialSol[..i], jobs, |partialSol[..i]|); //help
                assert dp[i - 1] >= PartialSolutionPrefixProfit(partialSol[..i], jobs, 0); //daca nu adaug job-ul i se obtine profitul dp[i-1]
                assert dp[i - 1] >= PartialSolutionPrefixProfit(partialSol, jobs, 0);
                assert dp[i - 1] < maxProfit; //care stim din preconditii ca este < maxProfit
                //assume false;
                //assume false;
                assert HasLessProfit(partialSol, jobs, maxProfit, 0);

                }
    
    }
}


method leadsToOptimalWithTakingJobI(jobs: seq<Job>, dp:seq<int>, allSol: seq<seq<int>>, i: int, maxProfit: int, partialSolWithJobI: seq<int>) returns (optimalPartialSolution: seq<int>, profits:seq<int>)
requires validJobsSeq(jobs)
requires sortedByActEnd(jobs)
requires distinctJobsSeq(jobs)
requires 1 <= i < |jobs|
requires |allSol| == i 
requires |dp| == i
requires OptimalPartialSolutions(allSol, jobs, dp, i)
requires dp[i-1] == PartialSolutionPrefixProfit(allSol[i-1], jobs, 0)
requires PositiveProfitsDP(dp)
requires isPartialSolution(partialSolWithJobI, jobs, i + 1)
requires partialSolutionWithJobI(partialSolWithJobI, jobs, i)
requires maxProfit == PartialSolutionPrefixProfit(partialSolWithJobI, jobs, 0);
requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
requires forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i //stim din invariant 
requires dp[i - 1] < maxProfit
ensures isPartialSolution(optimalPartialSolution, jobs, i + 1)
ensures PositiveProfitsDP(profits)
ensures |profits| == i + 1
ensures profits == dp + [maxProfit]
ensures |optimalPartialSolution| == i + 1
ensures 2 <= |profits| <= |jobs|
ensures profits[i] == maxProfit
ensures HasProfit(optimalPartialSolution, jobs, 0, profits[i])
//ensures profits[i] == PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0)
ensures isOptimalPartialSolution(optimalPartialSolution, jobs, i + 1) 
ensures forall partialSol :: |partialSol| == i + 1  && isPartialSolution(partialSol, jobs, i + 1) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
ensures partialSolutionWithoutJobI(optimalPartialSolution, jobs, i) ==> PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0) == PartialSolutionPrefixProfit(optimalPartialSolution[..|optimalPartialSolution|-1], jobs, 0)
{   
    profits := dp + [maxProfit]; //profitul general creste deorece cu job-ul curent se obtine un profit mai mare 

    assert partialSolWithJobI[i] == 1;
    optimalPartialSolution := partialSolWithJobI; //solutia contine job-ul i 
    // assume false;
    
    assert isPartialSolution(optimalPartialSolution, jobs, i + 1);
    
    assert PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0) == maxProfit;
    
    assert profits[i] == PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0);

    assert profits[i] == maxProfit;
    
    assert partialSolutionWithJobI(optimalPartialSolution, jobs, i);
    
    //stim din functia max_profit ca aceasta solutie ce contine job-ul i este solutia optima (cu job-ul i)
    assert  optimalPartialSolution[i] == 1;

    //assume false;
    //demonstram ca aceasta solutie partiala este si optima 
    optimalPartialSolutionWithJobI(i, jobs, maxProfit, allSol, dp);
    // forall partialSol | |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|)
    // ensures HasLessProfit(partialSol, jobs, profits[i], 0);
    // {   
    //     if partialSol[i] == 1
    //     {   
    //         assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0);
    //         //assume false;
    //         //demonstrat din functia MaxProfitWithJobI
    //     }
    //     else{
    //             //daca nu adaug un job profitul ramane <= dp[i-1] (invariant sulutie partiala optima), care in aceasta ramura a if-ului este <= max_profit 
    //             // ==> tranzitivitate ==> profitul curent <= dp[i] (= max_profit)
    //             //nu se demonstreaza 
    //             //daca nu punem job-ul i => punem 0 si profitul este <= dp[i-1] (optim) (pasul anterior), dp[i - 1] < max_profit => tranzitivitate <= max_profit
    //             NotAddingAJobKeepsSameProfit(partialSol[..i], jobs, 0);
    //             assert partialSol[..i] + [0] == partialSol;
    //             assert PartialSolutionPrefixProfit(partialSol[..i], jobs, 0) == PartialSolutionPrefixProfit(partialSol, jobs, 0);
    //             assert OptimalPartialSolutions(allSol, jobs, dp, i);
    //             assert isOptimalPartialSolution(allSol[i - 1], jobs, |allSol[i - 1]|);
    //             assert PartialSolutionPrefixProfit(allSol[i - 1], jobs, 0) == dp[i - 1];
    //             assert HasProfit(allSol[i - 1], jobs, 0,  dp[i - 1]); 
    //             //SubSeqOfPartialIsAlsoPartial(partialSol, jobs, i);
    //             assume isPartialSolution(partialSol[..i], jobs, |partialSol[..i]|); //help
    //             //assume false;
    //             assert dp[i - 1] >= PartialSolutionPrefixProfit(partialSol[..i], jobs, 0); //daca nu adaug job-ul i se obtine profitul dp[i-1]
    //             assert dp[i - 1] >= PartialSolutionPrefixProfit(partialSol, jobs, 0);
    //             assert dp[i - 1] < maxProfit; //care stim din preconditii ca este < maxProfit
    //             //assume false;
    //             }
    
    // }
    //assume false;
    //assert maxProfit == profits[i];
    assert forall partialSol :: |partialSol| == i + 1   && isPartialSolution(partialSol, jobs, i + 1) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
    assert isOptimalPartialSolution(optimalPartialSolution, jobs, i + 1);
}

//DEMONSTRATA
method leadsToOptimalWithoutTakingJobI(jobs: seq<Job>, dp:seq<int>, allSol: seq<seq<int>>, i: int, maxProfit: int, partialSol: seq<int>, partialSolWithJobI: seq<int>) returns (optimalPartialSolution: seq<int>, profits:seq<int>)
requires validJobsSeq(jobs)
requires sortedByActEnd(jobs)
requires distinctJobsSeq(jobs)
requires 1 <= i < |jobs|
requires |allSol| == i 
requires |dp| == i
requires OptimalPartialSolutions(allSol, jobs, dp, i)
requires dp[i-1] == PartialSolutionPrefixProfit(allSol[i-1], jobs, 0)
requires PositiveProfitsDP(dp)
requires |partialSol| == i
requires isOptimalPartialSolution(partialSol, jobs, i)
requires isPartialSolution(partialSol, jobs, i) //corectie
requires isPartialSolution(partialSolWithJobI, jobs, i + 1)
requires partialSolutionWithJobI(partialSolWithJobI, jobs, i)
requires maxProfit == PartialSolutionPrefixProfit(partialSolWithJobI, jobs, 0)
requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
requires forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i 
requires dp[i - 1] >= maxProfit
ensures isPartialSolution(optimalPartialSolution, jobs, i + 1)
ensures isOptimalPartialSolution(optimalPartialSolution, jobs, i + 1)
ensures profits == dp + [dp[i-1]]
ensures |profits| == i + 1
ensures |optimalPartialSolution| == i + 1
ensures 2 <= |profits| <= |jobs|
ensures profits[i] == PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0)
ensures HasProfit(optimalPartialSolution, jobs, 0, profits[i])
ensures forall partialSol :: |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
ensures partialSolutionWithoutJobI(optimalPartialSolution, jobs, i) ==> PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0) == PartialSolutionPrefixProfit(optimalPartialSolution[..|optimalPartialSolution|-1], jobs, 0)
{   
    //demonstram ca dp[i - 1] este maxim folosindu-ne de ce stim de la pasul anterior (toate profiturile posibile <= dp[i-1] )
    //daca nu adaugam un job, profitul ramane acelasi cu cel anterior care este <= dp[i-1] ==> conditia se pastreaza dp[i] = dp[i-1]
    assert dp[i-1] >= maxProfit;
    
    AssociativityOfProfitFunc(partialSol, jobs, 0, 0);
    
    profits := dp + [dp[i-1]]; //profitul maxim ramane profitul anterior deoarece prin prin selectarea job-ului curent nu se obtine un profit mai mare  
    
    assert profits[i] == dp[i - 1];

    assert |partialSol| < |jobs|;
    
    NotAddingAJobKeepsSameProfit(partialSol, jobs, 0);
    
    optimalPartialSolution := partialSol + [0]; //solutia nu contine job-ul i 
    
    assert isPartialSolution(optimalPartialSolution, jobs, i + 1); //aiic demonstram ca este solutie partiala
    
    assert profits[i] == PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0);

    assert partialSolutionWithoutJobI(optimalPartialSolution, jobs, i);

    forall partialSol | |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|)
    ensures HasLessProfit(partialSol, jobs, profits[i], 0) //profits[i] == dp[i - 1] => imi doresc sa arat ca se obtin profituri <= dp[i-1] si am reusit YEEEE:))
    {   
        if partialSol[i] == 1
        {   
            //assume false;
            //stim ca toate au profitul <= max_profit, iar max_profit <= dp[i-1]
            assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0);
            assert maxProfit <= dp[i - 1];
            assert profits[i] == dp[i - 1];
            assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
            //assume false;
        }
        else
        {   
            assert partialSol[i] == 0;
            //daca adugam 0 profitul ramane acelasi cu profitul de inainte de a adauga job-ul <= dp[i-1] (pasul anterior) <= dp[i - 1] SMART 
            //profitul ramane dp[i-1] care stim ca este optim pentru toate solutiile partiale de lungime i - 1 din invariant 
            NotAddingAJobKeepsSameProfit(partialSol[..i], jobs, 0);
            assert partialSol[..i] + [0] == partialSol;
            assert PartialSolutionPrefixProfit(partialSol[..i], jobs, 0) == PartialSolutionPrefixProfit(partialSol, jobs, 0); //<= dp[i-1] IMPORTANT
            assert isOptimalPartialSolution(allSol[i - 1], jobs, |allSol[i - 1]|);
            assert PartialSolutionPrefixProfit(allSol[i - 1], jobs, 0) == dp[i - 1]; //profitul optim 
            //assume false;
            assert isPartialSolution(partialSol[..i], jobs, |partialSol[..i]|);
            assert dp[i - 1] >= PartialSolutionPrefixProfit(partialSol[..i], jobs, 0); //dp[i-1] profit optim ..i !!IMPORTANT
            assert forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0);
            //assert dp[i] == dp[i - 1];
            //assume false;
            // profit partialSol == profit (partialSol fara ultimul element)
            //                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
            //                       optim din invariantul pentru allSol
            //assume false;
        }
    }
    //assume false;
    assert isOptimalPartialSolution(optimalPartialSolution, jobs, i + 1);
    assert forall partialSol :: |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
    }



method WeightedJobScheduling(jobs: seq<Job>) returns (sol: seq<int>, profit : int)
    requires 1 <= |jobs|
    requires validJobsSeq(jobs)
    requires distinctJobsSeq(jobs)
    requires sortedByActEnd(jobs)
    ensures isSolution(sol, jobs)
    ensures isOptimalSolution(sol, jobs)
{   
    var dp :seq<int> := [];
    
    var dp0 := jobs[0].profit; //profitul primului job
    
    dp := dp + [dp0]; 
    
    var solution : seq<int> := [1]; //solutia optima de lungime 1 
    
    var i: int := 1;
    
    var allSol : seq<seq<int>> := []; //stocam toate solutiile partiale optime
    
    allSol := allSol + [[1]]; //adaugam solutia partiala optima de lungime 1 
    
    assert |solution| == 1;
    assert |allSol[0]| == |solution|;
    assert 0 <= solution[0] <= 1;
    
    assert isPartialSolution(solution, jobs, i);
    
    assert validJob(jobs[0]); //profit >=0 
    
    assert isOptimalPartialSolution(solution, jobs, i); //[1] solutia optima de lungime 1 
    while i < |jobs| 
        invariant 1 <= i <= |jobs|
        decreases |jobs| - i
        invariant i == |dp|  //am demonstrat
        invariant 1 <= |dp| <= |jobs| //am demonstrat
        decreases |jobs| - |dp|
        invariant isPartialSolution(solution, jobs, i) //am demonstrat 
        invariant |solution| == i //am demonstrat
        invariant i == |allSol| //am demonstrat
        decreases |jobs| - |allSol|
        invariant |allSol[i-1]| == i // trivial
        invariant forall k :: 0 <= k < i ==> |allSol[k]| == k + 1 //trivial
        invariant 1 <= |allSol[i-1]| <= |jobs| //trivial
        decreases |jobs| - |allSol[i-1]| 
        invariant isPartialSolution(allSol[i-1], jobs, i)
        invariant ValidPartialSolutions(allSol, jobs, i) //i = 1, allSol are lungime 1 , deci doar AllSol[0] exista 
        invariant dp[i-1] == PartialSolutionPrefixProfit(solution, jobs, 0) //trebuie sa ne asiguram ca se demonstreaza in urm metodelor apelate
        invariant dp[i-1] == PartialSolutionPrefixProfit(allSol[i-1], jobs, 0)
        invariant HasProfit(solution, jobs, 0, dp[i - 1])
        invariant HasProfit(allSol[i - 1], jobs, 0 , dp[i - 1])
        invariant allSol[i - 1] == solution
        invariant OptimalPartialSolutions(allSol, jobs, dp, i)
        invariant isOptimalPartialSolution(allSol[i - 1], jobs, i)   //solution este de lungime i
        invariant partialSolutionWithoutJobI(solution, jobs, i - 1) ==> PartialSolutionPrefixProfit(solution, jobs, 0) == PartialSolutionPrefixProfit(solution[..|solution|- 1], jobs, 0)
        invariant forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //sol par optima
        invariant forall i :: 0 <= i < |dp| ==> dp[i] >= 0 
        invariant isOptimalPartialSolution(solution, jobs, i)
    {  
        //castigul pt sol partiala este dp
        var maxProfit, partialSolWithI := MaxProfitWithJobI(jobs, i, dp, allSol); 

        assert maxProfit == PartialSolutionPrefixProfit(partialSolWithI, jobs, 0);
        assert partialSolutionWithJobI(partialSolWithI, jobs, i);
        //calculeaza maximul dintre excluded profit si included profit 
        //maximul dintre profitul obtinut pana la job-ul anterior si profitul obtinut cu adugarea job-ului curent  
        
        if dp[i-1] >= maxProfit //se obtine un profit mai bun fara job-ul curent //lemma requires conditia
        {   
            //assume false;
            assert validJobsSeq(jobs);
            assert sortedByActEnd(jobs);
            assert distinctJobsSeq(jobs);
            assert 1 <= i < |jobs|;
            assert |allSol| == i; 
            assert |dp| == i;
            assert OptimalPartialSolutions(allSol, jobs, dp, i);
            assert PositiveProfitsDP(dp);
            assert |solution| == i;
            assert isOptimalPartialSolution(solution, jobs, i);
            assert isPartialSolution(solution, jobs, i); //corectie
            assert isPartialSolution(partialSolWithI, jobs, i + 1);
            assert partialSolutionWithJobI(partialSolWithI, jobs, i);
            assert maxProfit == PartialSolutionPrefixProfit(partialSolWithI, jobs, 0);
            assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0);
            assert forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i 
            assert dp[i - 1] >= maxProfit;
            //assume false;
            solution, dp := leadsToOptimalWithoutTakingJobI(jobs, dp, allSol, i, maxProfit, solution, partialSolWithI);
        }
        else //alegem job-ul i dp[i-1] < maxProfit
        {   
            //assume false;
            assert validJobsSeq(jobs);
            assert sortedByActEnd(jobs);
            assert distinctJobsSeq(jobs);
            assert 1 <= i < |jobs|;
            assert |allSol| == i ;
            assert |dp| == i;
            assert OptimalPartialSolutions(allSol, jobs, dp, i);
            assert PositiveProfitsDP(dp);
            assert isPartialSolution(partialSolWithI, jobs, i + 1);
            assert partialSolutionWithJobI(partialSolWithI, jobs, i);
            assert maxProfit == PartialSolutionPrefixProfit(partialSolWithI, jobs, 0);
            assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0);
            assert forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i 
            assert dp[i - 1] < maxProfit;
            //assume false;
            solution, dp := leadsToOptimalWithTakingJobI(jobs, dp, allSol, i, maxProfit, partialSolWithI);
            assert isOptimalPartialSolution(solution, jobs, i + 1);
            
        }
        print("Sol: ", solution);
        print("DP: ", dp);
        //assert dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i);
        allSol := allSol + [solution]; //cream secventa de solutii(care includ job-ul curent sau nu) pentru fiecare job in parte 
        //allSol[j] = contine solutia partiala optima pana la pozitia j inclusiv (formata din job-urile pana la pozitia j inclusiv, partiala optima)
        print("Allsol: ", allSol);
        //assert isPartialSolution(allSol[i-1], jobs, i);
        //assert ValidPartialSolutions(allSol, jobs, i+1);
        i := i + 1;
    }

    sol := solution;
    profit := dp[|dp|-1]; //ultimul profit este maxim  
}


method Main()
{   
    var job1: Job := Pair(jobStart := 1, jobEnd := 2, profit := 50);
    var job2: Job := Pair(jobStart := 3, jobEnd := 5, profit := 20);
    var job3: Job := Pair(jobStart := 6, jobEnd := 19, profit := 100);
    var job4: Job := Pair(jobStart := 2, jobEnd := 100, profit := 200);
    var jobs: seq<Job> := [job1, job2, job3, job4];
    // var job1: Job := Pair(jobStart := 0, jobEnd := 10, profit := 1);
    // var job2: Job := Pair(jobStart := 15, jobEnd := 25, profit := 1);
    // var job3: Job := Pair(jobStart := 30, jobEnd := 40, profit := 1);
    // var job4: Job := Pair(jobStart := 20, jobEnd := 50, profit := 1);
    // var job5: Job := Pair(jobStart := 60, jobEnd := 70, profit := 1);
    // var jobs: seq<Job> := [job1, job2, job3, job4, job5];
    // print(jobs[..1]);
    // print(|jobs[..1]|);
    var s : seq<seq<int>> := [[1, 2, 2]];
    var partial : seq<int> := [0,0,1];
    var partial' : seq<int> := [0,0,0,1];
    var profit : int :=  PartialSolutionProfit(partial, jobs, 0, 1);
    var profit' : int :=  PartialSolutionProfit(partial', jobs, 0, 0);
    print(profit);
    print(profit');
    assert profit == profit';
    assert PartialSolutionPrefixProfit([0,0,1], jobs, 1) == jobs[2].profit;

    // //s := s + [[2]];
    // // print(s);
    // print(|s|);
    // var secventa : seq<int> := [1,1,1];
    // // print(s[0]);
    // //secventa de job-uri trebuie sa fie valida (1)
    // //-----------------------------------contina job-uri diferite din pctdv al cel putin un timp (st sau sf)  
    // var solutie : seq<int> := [];
    // //var profit : int := 0;
    // solutie, profit := WeightedJobScheduling(jobs);
    // print ("Solutia: ", solutie);
    // //solutia trebuie sa contina job-uri care nu se suprapun si sa fie de profit maxim 
    
}
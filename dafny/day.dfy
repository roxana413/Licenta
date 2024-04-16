datatype Job = Tuple(jobStart: int, jobEnd: int, profit: int)

predicate validProblem(jobs: seq<Job>)
{
  1 <= |jobs| && validJobsSeq(jobs) && sortedByActEnd(jobs) && distinctJobsSeq(jobs)
}

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

predicate  distinctJobs(j1: Job, j2: Job)
  requires validJob(j1) && validJob(j2)
{
  j1.jobStart != j2.jobStart || j1.jobEnd != j2.jobEnd
}

predicate distinctJobsSeq(s: seq<Job>)
  requires validJobsSeq(s)
{
  forall i, j :: 0 <= i < j < |s| ==> distinctJobs(s[i], s[j])
}


predicate overlappingJobs(j1:Job, j2:Job)
  requires validJob(j1)
  requires validJob(j2)
{
  j1.jobEnd > j2.jobStart &&  j2.jobEnd > j1.jobStart //j1.jobEnd <= j2.jobStart || j2.jobEnd <= j1.jobStart
  //primul job se termina inainte ca al 2-lea sa inceapa (j1, j2), si primul job incepe inainte ca al 2-lea sa se termine (j2, j1)
  //ele fiind deja ordonate dupa timpul de finish
}


predicate sortedByActEnd(s: seq<Job>)
  requires validJobsSeq(s)
{
  forall i, j :: 0 <= i < j < |s| ==> JobComparator(s[i], s[j])
}


function SolutionProfit(solution: seq<int>, jobs: seq<Job>, index: int): int
  requires |solution| == |jobs|
  requires 0 <= index <= |solution|
  requires 1 <= |jobs|
  decreases |solution| - index
  ensures SolutionProfit(solution, jobs, index ) == if index == |solution| then 0 else solution[index] * jobs[index].profit + SolutionProfit(solution, jobs, index + 1)
{

  if index == |solution| then 0 else solution[index] * jobs[index].profit + SolutionProfit(solution, jobs, index + 1)
}


function PartialSolutionPrefixProfit(solution: seq<int>, jobs: seq<Job>, index: int): int
  requires 0 <= index <= |solution| <= |jobs|
  decreases |solution| - index
  ensures PartialSolutionPrefixProfit(solution, jobs, index) == if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionPrefixProfit(solution, jobs, index + 1)
{

  if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionPrefixProfit(solution, jobs, index + 1)
}


predicate hasNoOverlappingJobs(partialSol: seq<int>, jobs: seq<Job>)
  requires validJobsSeq(jobs)
{
  |partialSol| <= |jobs|  && forall i, j :: 0 <= i < j < |partialSol| ==> (partialSol[i] == 1 && partialSol[j] == 1) ==> !overlappingJobs(jobs[i], jobs[j])
}

// predicate hasNoOverlappingJobs2(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)//schimb nume
//   requires validJobsSeq(jobs)
//   requires 0 <= j <= i < |jobs|
//   requires i - j + 1 == |partialSol|
// {
//   |partialSol| <= |jobs|  && forall x, y :: 0 <= x < y < |partialSol| ==>
//                                               (partialSol[x] == 1 && partialSol[y] == 1) ==> !overlappingJobs(jobs[j + x], jobs[j + y])
// }

predicate areOrderedByEnd(partialSol: seq<int>, jobs: seq<Job>)
  requires validJobsSeq(jobs)
{
  |partialSol| <= |jobs|  && forall i, j :: 0 <= i < j < |partialSol| ==>
                                              (partialSol[i] == 1 && partialSol[j] == 1) ==> JobComparator(jobs[i], jobs[j])
}

// predicate areOrderedByEnd2(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
//   requires validJobsSeq(jobs)
//   requires 0 <= j <= i < |jobs|
//   requires i - j + 1 == |partialSol|
// {
//   |partialSol| <= |jobs|  && forall x, y :: 0 <= x < y < |partialSol| ==>
//                                               (partialSol[x] == 1 && partialSol[y] == 1) ==> JobComparator(jobs[j + x], jobs[j + y])
// }


//demonstram ca functia profit este asociativa prin inductie
lemma AssociativityOfProfitFunc(partialSolPrefix : seq<int>, jobs: seq<Job>, val: int, index: int)
  requires 1 <= |jobs|
  requires validJobsSeq(jobs)
  requires 0 <= index <= |partialSolPrefix|
  requires 0 <= val <= 1
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
{   
  |partialSol| == length &&
  forall i :: 0 <= i <= |partialSol| - 1 ==> (0 <= partialSol[i] <= 1) && hasNoOverlappingJobs(partialSol, jobs)
}


// predicate ValidPartialSolutions(allSol:seq<seq<int>>, jobs: seq<Job>,  index: int)
//   requires validJobsSeq(jobs)
// {
//   |allSol| == index && forall i : int :: 0 <= i < index ==> isPartialSolution(allSol[i], jobs, i + 1) //pana la i + 1 inseamna pana la 2 -> 0 1

// }


ghost predicate isOptimalPartialSolution(partialSol: seq<int>, jobs: seq<Job>, length: int)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs| 
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
  requires 1 <= length <= |jobs|
{
  |partialSol| == length && isOptimalPartialSolution(partialSol, jobs, length) && HasProfit(partialSol, jobs, 0,  dp)
}

ghost predicate OptimalPartialSolutions(allSol: seq<seq<int>>, jobs: seq<Job>, dp:seq<int>, index: int)
  requires validJobsSeq(jobs)
  requires |dp| == |allSol| == index
  requires 1 <= index <= |jobs|
{
  forall i : int :: 0 <= i < index ==> |allSol[i]| == i + 1  && isOptimalPartialSolutionDP(allSol[i], jobs, i + 1, dp[i])
}

predicate isSolution(solution: seq<int>, jobs: seq <Job>)
  requires validJobsSeq(jobs)
{
  isPartialSolution(solution, jobs, |jobs|)
}


ghost predicate isOptimalSolution(solution: seq<int>, jobs: seq<Job>)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires |solution| == |jobs|
{
  isSolution(solution, jobs) &&
  forall otherSol :: isSolution(otherSol, jobs) ==>  PartialSolutionPrefixProfit(solution, jobs, 0) >=  PartialSolutionPrefixProfit(otherSol, jobs, 0)
}

// predicate isOptimalSolutionDP(solution: seq<int>, jobs: seq<Job>, dp: int)
//   requires 1 <= |jobs|
//   requires validJobsSeq(jobs)
//   requires |solution| == |jobs|
// {
//   isSolution(solution, jobs) && SolutionProfit(solution, jobs, 0) == dp
// }

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
  requires 0 <= position < |partialSol| <= |jobs|
{
  PartialSolutionPrefixProfit(partialSol, jobs, position) <= maxProfit
}

predicate HasMoreProfit(partialSol: seq<int>, jobs: seq<Job>,  maxProfit: int, position: int)
  requires validJobsSeq(jobs)
  requires 0 <= position < |partialSol| <= |jobs|
{
  PartialSolutionPrefixProfit(partialSol, jobs, position) > maxProfit
}


function ProfitParSolStartFinishPos(solution: seq<int>, jobs: seq<Job>, startPos: int, endPos: int): int
  requires 0 <= startPos <= endPos <= |solution| <= |jobs|
  decreases |solution| - startPos
  ensures ProfitParSolStartFinishPos(solution, jobs, startPos, endPos) == if startPos == endPos then 0 else solution[startPos] * jobs[startPos].profit + ProfitParSolStartFinishPos(solution, jobs, startPos + 1, endPos)
{

  if startPos == endPos then 0 else solution[startPos] * jobs[startPos].profit + ProfitParSolStartFinishPos(solution, jobs, startPos + 1, endPos)
}

// + o lemma in care demonstres PartialSolutionPrefix(partialSol, jobs, j + 1) ==  ProfitParSolStartFinishPos(solution, jobs, j + 1, |solution|) //scoatem jobs[i].profits
//PartialSolutionPrefix(partialSol, jobs, 0) ==  ProfitParSolStartFinishPos(solution, jobs, 0, |solution|) + lemma
//PartialSolutionPrefix(partialSol[..j+1], jobs, 0) ==  ProfitParSolStartFinishPos(solution, jobs, 0, j + 1) + lemma
lemma EqOfProfitFuncFromIndToEnd(partialSolution: seq<int>, jobs: seq<Job>, startPos: int)
  requires 0 <= startPos <= |partialSolution|  <= |jobs|
  ensures ProfitParSolStartFinishPos(partialSolution, jobs, startPos, |partialSolution|) == PartialSolutionPrefixProfit(partialSolution, jobs, startPos)
  decreases |partialSolution| - startPos
{

  if startPos == |partialSolution|
  {

  }
  else
  {
    EqOfProfitFuncFromIndToEnd(partialSolution, jobs, startPos + 1);
  }
}


lemma EqOfProfFuncUntilIndex(partialSolution: seq<int>, jobs: seq<Job>, startPos: int, index: int) //PartialSolutionPrefixProfit(partialSol[..j+1], jobs, 0)
  requires 0 <= startPos <= index <= |partialSolution| <= |jobs|
  ensures  ProfitParSolStartFinishPos(partialSolution, jobs, startPos, index) == PartialSolutionPrefixProfit(partialSolution[..index], jobs, startPos)
  decreases index - startPos
{
  if startPos == index{
    assert ProfitParSolStartFinishPos(partialSolution, jobs, startPos, index) == 0;
  }
  else{
    EqOfProfFuncUntilIndex(partialSolution, jobs, startPos + 1, index);
  }
}


lemma SplitSequenceProfitEquality(partialSol: seq<int>, jobs: seq<Job>, startPos: int, index: int)
  requires 0 <= index < |partialSol|
  requires 0 <= startPos < index
  requires 0 <= |partialSol| <= |jobs|
  ensures ProfitParSolStartFinishPos(partialSol, jobs, startPos, |partialSol|) == ProfitParSolStartFinishPos(partialSol, jobs, startPos, index) + ProfitParSolStartFinishPos(partialSol, jobs, index, |partialSol|)
  decreases  index - startPos
{
  
}

lemma ProfitLastElem(partialSol: seq<int>, jobs: seq<Job>, i: int)
  requires validJobsSeq(jobs)
  requires 0 < i < |partialSol| <= |jobs|
  requires |partialSol| == i + 1
  requires partialSolutionWithJobI(partialSol, jobs, i)
  ensures PartialSolutionPrefixProfit(partialSol, jobs, i) == jobs[i].profit
{
}


lemma ComputeProfitWhenOnly0BetweenJI(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
  requires validJobsSeq(jobs)
  requires 0 <= j < i < |partialSol| <= |jobs|
  requires |partialSol| == i + 1
  requires isPartialSolution(partialSol, jobs, |partialSol|)
  requires partialSolutionWithJobI(partialSol, jobs, i)
  requires PartialSolutionPrefixProfit(partialSol, jobs, i) == jobs[i].profit
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
    // assert partialSol[i] == 1;
    // assert PartialSolutionPrefixProfit(partialSol, jobs, i) == jobs[i].profit;
    // assert forall k :: j < k < i ==> partialSol[k] == 0;
    ComputeProfitWhenOnly0BetweenJI(partialSol, jobs, i, j + 1);
    //assert PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == jobs[i].profit;
  }

}

lemma HasMoreProfitThanOptimalPartialSol(optimalPartialSol: seq<int>, jobs: seq<Job>, partialSol: seq<int>)
  requires validJobsSeq(jobs)
  requires 1 <= |optimalPartialSol| <= |jobs|
  requires |optimalPartialSol| == |partialSol|
  requires isPartialSolution(partialSol, jobs, |partialSol|)
  requires isOptimalPartialSolution(optimalPartialSol, jobs, |optimalPartialSol|)
  requires PartialSolutionPrefixProfit(partialSol, jobs, 0) > PartialSolutionPrefixProfit(optimalPartialSol, jobs, 0)
  ensures !isOptimalPartialSolution(optimalPartialSol, jobs, |optimalPartialSol|)
{
  var other_profit := PartialSolutionPrefixProfit(partialSol, jobs, 0);
  var optimalPartialSolProfit := PartialSolutionPrefixProfit(optimalPartialSol, jobs, 0);
  assert forall otherSol:: isPartialSolution(otherSol, jobs, |optimalPartialSol|) ==> HasLessProfit(otherSol, jobs, optimalPartialSolProfit, 0);
  assert other_profit > optimalPartialSolProfit;
  assert !isOptimalPartialSolution(optimalPartialSol, jobs, |optimalPartialSol|);

}

//suntem in cazul in care cand formam solutia partiala cu job-ul i, gasim o solutie partiala optima cu care facem concatenare
//demonstram ca pentru aceste date, j nu se suprapune cu i + solutie partiala ce-l contine pe i + concatenare cu allSol[j] partiala optima, aceasta este optima
lemma OtherSolHasLessProfitThenMaxProfit2(partialSol: seq<int>, jobs : seq<Job>, i: int, j : int, max_profit : int, allSol : seq<seq<int>>, dp: seq<int>)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires 0 <= j < i < |jobs|
  requires |allSol| == |dp| == i  //nr de profituri optime pentru solutiile partiale optime din fata lui este egal i
  requires OptimalPartialSolutions(allSol, jobs, dp, i)
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
  //assert !exists k' :: k < k' < i;

  assert forall k' :: k < k' < i ==> partialSol[k'] == 0; //asta vreau sa demonstrez ==> ca am doar 0 -rouri pe pozitiile i - 1 ...0
  assert PartialSolutionPrefixProfit(partialSol, jobs, i) == jobs[i].profit;

  ComputeProfitWhenOnly0BetweenJI(partialSol, jobs, i, j);
  assert PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == jobs[i].profit;
  
  //presupunem contrariul
  if !HasLessProfit(partialSol, jobs, max_profit, 0) //presupunem ca ar exista o solutie partiala care indeplineste conditiile si care
    //sa aiba profitul mai mare decat max_profit
  {
    var profit' := PartialSolutionPrefixProfit(partialSol, jobs, 0);
    assert max_profit == dp[j] + jobs[i].profit;

    assert HasMoreProfit(partialSol, jobs, max_profit, 0);
    assert !HasLessProfit(partialSol, jobs, max_profit, 0);
    
    assert partialSol[..j+1] + partialSol[j+1..] == partialSol;
    //apelam lemmele ajutatoare pt a demonstra linia 400
    SplitSequenceProfitEquality(partialSol, jobs, 0, j + 1);
    EqOfProfitFuncFromIndToEnd(partialSol, jobs, 0);
    EqOfProfFuncUntilIndex(partialSol, jobs, 0, j + 1);
    EqOfProfitFuncFromIndToEnd(partialSol, jobs, j + 1);
  
    assert PartialSolutionPrefixProfit(partialSol[..j + 1], jobs, 0) + PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == PartialSolutionPrefixProfit(partialSol, jobs, 0);
    assert PartialSolutionPrefixProfit(partialSol, jobs, j + 1) == jobs[i].profit; //(2)
    
    var partialSol' :seq<int> := partialSol[..j + 1];
    assert isPartialSolution(partialSol', jobs, j + 1);
    var profit := PartialSolutionPrefixProfit(partialSol', jobs, 0); //(1)

    assert |partialSol'| == j + 1;
    assert profit + jobs[i].profit == profit'; //(linia 400)
    assert profit + jobs[i].profit > max_profit; //ipoteza de la care am plecat 
    assert profit > max_profit - jobs[i].profit;
    assert profit > dp[j];
    HasMoreProfitThanOptimalPartialSol(allSol[j], jobs, partialSol');
    assert !isOptimalPartialSolution(allSol[j], jobs, j + 1); //contradictie
    //assume false;
    assert false;
  }

  assert HasLessProfit(partialSol, jobs, max_profit, 0);

}
//demonstram ca daca toate job-urile dintre i si j se suprapun este imposibil sa avem 1 (=> suprapunere=> !solutie partiala)
lemma OnlY0WhenOverlapJobs(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
  requires validJobsSeq(jobs)
  requires isPartialSolution(partialSol, jobs, i + 1)
  requires 0 <= j < i < |partialSol|  <= |jobs|
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

//demonstram ca niciun job din allSol[j] nu se suprapune cu i, stiind ca j nu se suprapune cu i
// lemma AddNotOverlappingSeq(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
//   requires validProblem(jobs)
//   requires |partialSol| < |jobs|
//   requires |partialSol| == j + 1; //allSol[j]
//   requires 0 <= j < i < |jobs|
//   requires jobs[j].jobEnd <= jobs[i].jobStart; // j nu se suprapune cu i
//   requires !overlappingJobs(jobs[j], jobs[i]) //jobs[j].actEnd <= jobs[i].actStart
//   requires isPartialSolution(partialSol, jobs, |partialSol|) //allSol[j] este solutie partiala
//   requires hasNoOverlappingJobs(partialSol, jobs)
//   ensures forall k :: 0 <= k < |partialSol| ==> partialSol[k] == 1 ==> !overlappingJobs(jobs[k], jobs[i])
// {
//   assert forall k, k' :: 0 <= k < k' <= j ==> jobs[k].jobEnd <= jobs[k'].jobEnd; //sunt sortate dupa timpul de sf
//   assert forall k :: 0 <= k <= j ==> validJob(jobs[k]);
//   assert forall k :: 0 <= k <= j ==> jobs[k].jobStart <= jobs[k].jobEnd; //sunt sortate dupa timpul de sf
//   assert !overlappingJobs(jobs[j], jobs[i]);
//   assert validJob(jobs[j]);
//   assert jobs[j].jobStart < jobs[j].jobEnd;
//   assert jobs[j].jobEnd <= jobs[i].jobStart;
//   assert jobs[j].jobStart < jobs[i].jobStart;
//   assert forall k :: 0 <= k <= j ==> jobs[k].jobEnd <= jobs[i].jobStart; //sunt sortate dupa timpul de sf
//   assert forall k :: 0 <= k <= j ==> partialSol[k] == 1 ==> !overlappingJobs(jobs[k], jobs[i]); //sunt sortate dupa timpul de sf
//   //assert hasNoOverlappingJobs(a, jobs);
// }

//demonstram ca solutia partiala optinuta prin concatenarea allSol[j] + 0000 + i nu contine job-uri care se suprapun
// lemma NotOverlappingJobsSeq(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
//   requires validProblem(jobs)
//   requires |partialSol| <= |jobs|
//   requires |partialSol| == i + 1;
//   requires 0 <= j < i < |jobs|
//   requires partialSol[i] == 1 //pe pozitia i avem 1
//   requires !overlappingJobs(jobs[j], jobs[i]) //jobs[j].actEnd <= jobs[i].actStart
//   requires isPartialSolution(partialSol[..j+1], jobs, j + 1) //allSol[j]
//   requires hasNoOverlappingJobs(partialSol[..j+1], jobs) //allSol[j] nu contine job-uri care se suprapun
//   requires forall k :: 0 <= k < |partialSol[..j + 1]| ==> partialSol[k] == 1 ==> !overlappingJobs(jobs[k], jobs[i]) //lemma anterioara
//   requires forall k :: j + 1 <= k < i ==> partialSol[k] == 0
//   ensures hasNoOverlappingJobs(partialSol, jobs)
//   ensures forall k :: 0 <= k < i ==> partialSol[k] == 1 ==> !overlappingJobs(jobs[k], jobs[i])
// {

// }

//gasim un job j care nu se suprapune cu i
//dp - secventa cu toate profiturile solutiilor partiale optime cu job-uri pana la pozitia 0, 1.., i-1
//allSol secventa de secvente (matrice) ce reprezinta solutiile optime de lungime 0, ... i-1, i cu job-urile pana la pozitia i excusiv
//demonstram ca solutia de lungime i+1 ce contine job-ul i care se obtine cu aceste preconditii este partiala + optima
method  OptimalPartialSolutionWhenNonOverlapJob(jobs: seq <Job>, i: int, dp: seq<int>, allSol :seq<seq<int>>, j : int) returns (maxProfit:int, partialSolution: seq<int>, length: int)
  requires validProblem(jobs)
  requires 0 <= j < i < |jobs|
  requires |allSol| == i
  requires |dp| == i
  requires OptimalPartialSolutions(allSol, jobs, dp, i)
  requires !overlappingJobs(jobs[j], jobs[i]);
  requires jobs[j].jobEnd <= jobs[i].jobStart
  requires forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]) //job-urile de pe pozitiile j+1..i-1 se suprapun cu i
  requires !overlappingJobs(jobs[j], jobs[i]);
  ensures isPartialSolution(partialSolution, jobs, i + 1)
  ensures partialSolutionWithJobI(partialSolution, jobs, i)
  ensures maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0)
  ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
  ensures length == i + 1;
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

  while nr_of_zeros > 0
    decreases nr_of_zeros
    invariant 0 <= nr_of_zeros <= i - |allSol[j]| //setam limitele pentru nr_of_zeros
    decreases i - length
    invariant |allSol[j]| <= length <= i //imp
    invariant |partialSolutionPrefix| == length
    invariant forall k :: 0 <= k <= length - 1 ==> 0 <= partialSolutionPrefix[k] <= 1
    invariant length < |jobs|;
    invariant length == i - nr_of_zeros
    invariant hasNoOverlappingJobs(partialSolutionPrefix, jobs)
    invariant forall k :: j < k < |partialSolutionPrefix| ==> partialSolutionPrefix[k] == 0
    invariant max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0)
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

  assert length == i;
  assert |partialSolutionPrefix| == i ;

  assert forall k :: j < k < i ==> partialSolutionPrefix[k] == 0;
  assert forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]); //stim ca toate job-urile strict mai mari decat j se suprapun cu i

  assert isPartialSolution(partialSolutionPrefix, jobs, i);

  //AddNotOverlappingSeq(allSol[j], jobs, i, j); //demonstram ca toate job-urile prezente in allSol[j] nu se suprapun cu i
  //NotOverlappingJobsSeq(partialSolutionPrefix + [1], jobs, i, j); //demonstram ca partialSolutionPrefix nu contine job-uri care sa se suprapuna
  assert hasNoOverlappingJobs(partialSolutionPrefix + [1], jobs);

  AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 1, 0); //apelam inainte sa adaugam 1
  partialSolutionPrefix := partialSolutionPrefix + [1]; //includem si job-ul i (solutia partiala ce contine job-ul i)
  length := length + 1;
  max_profit := max_profit + jobs[i].profit;

  assert isPartialSolution(partialSolutionPrefix, jobs, i + 1);
  assert max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0); //lemma
  forall partialSol | |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i)
    ensures HasLessProfit(partialSol, jobs, max_profit, 0)
  {
    //assume forall k :: j < k < i ==> partialSol[k] == 0;
    OnlY0WhenOverlapJobs(partialSol, jobs, i, j); //stim ca daca toate job-urile dintre i si j se suprapun, inseamna ca putem avea doar 0-uri
    assert forall k :: j < k < i ==> partialSol[k] == 0;
    ProfitLastElem(partialSol, jobs, i);
    assert PartialSolutionPrefixProfit(partialSol, jobs, i) == jobs[i].profit;
    OtherSolHasLessProfitThenMaxProfit2(partialSol, jobs, i, j, max_profit, allSol, dp);
    //assume false;
  }

  //assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit, 0) ;
  maxProfit := max_profit;
  partialSolution := partialSolutionPrefix;
}

//lemma ajutor pt functia de mai jos
//HasLessProfit = <=
//demonstram ca daca toate job-urile din fata lui i se suprapun cu acesta nu putem avea decat 0 => 1 imposibil (!solutie partiala)
//=> profitul maxim pentru o astfel de solutie partiala este maxim jobs[i].profit
lemma OtherSolHasLessProfitThenMaxProfit(jobs : seq<Job>, i: int, max_profit : int)
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
    //assert !exists k' :: k < k' < i;
    assert forall k' :: k < k' < i ==> partialSol[k'] == 0; //asta vreau sa demonstrez ==> ca am doar 0 -rouri pe pozitiile i - 1 ...0
    assert PartialSolutionPrefixProfit(partialSol, jobs, k + 1) == jobs[i].profit;

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
//demonstram ca solutia de lungime i+1 ce contine job-ul i care se obtine cu aceste preconditii este partiala + optima
method  OptimalPartialSolutionWhenOverlapJob(jobs: seq <Job>, i: int, dp: seq<int>) returns (maxProfit:int, partialSolution: seq<int>, length: int)
  requires validProblem(jobs)
  requires 1 <= i < |jobs|
  requires |dp| == i
  requires forall k :: -1 < k < i ==> overlappingJobs(jobs[k], jobs[i]) //toate job-urile se suprapun cu i 
  ensures isPartialSolution(partialSolution, jobs, i + 1)
  ensures maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0)
  ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
  ensures length == i + 1;
  ensures partialSolutionWithJobI(partialSolution, jobs, i)
{
  // assume false;
  var partialSolutionPrefix : seq<int> := [];
  var max_profit : int := 0 ;
  length := 0;

  assert forall k :: -1 < k < i ==> overlappingJobs(jobs[k], jobs[i]);

  var nr_of_zeros := i;
  
  while nr_of_zeros > 0
    decreases nr_of_zeros
    decreases i - length
    invariant 0 <= nr_of_zeros <= i
    invariant |partialSolutionPrefix| == length
    invariant forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
    invariant length == i - nr_of_zeros
    invariant 0 <= length <= i
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
  assert partialSolutionWithJobI(partialSolutionPrefix + [1], jobs, i);

  assert forall k :: 0 <= k < i ==> partialSolutionPrefix[k] == 0; 
  assert forall k :: 0 <= k < i ==> overlappingJobs(jobs[k], jobs[i]); //preconditie
  
  assert isPartialSolution(partialSolutionPrefix, jobs, i);

  AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 1, 0); //apelata pentru max_profit inainte de a adauga 1 

  partialSolutionPrefix := partialSolutionPrefix + [1]; //includem si job-ul i (solutia partiala ce contine job-ul i)
  max_profit := max_profit + jobs[i].profit; //contine doar job-ul i
  length := length + 1;
  
  OtherSolHasLessProfitThenMaxProfit(jobs, i, max_profit); //demonstram optimalitatea 
  assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit, 0) ;

  //assert |partialSolutionPrefix| == i + 1;
  assert max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0);
  assert isPartialSolution(partialSolutionPrefix, jobs, length);

  partialSolution := partialSolutionPrefix;
  maxProfit := max_profit;
}

//predicat care pentru a fi respectat trebuie ca toate profiturile dp sa fie strict >= 0
predicate PositiveProfitsDP(dp: seq<int>)
{
  forall i :: 0 <= i < |dp| ==> dp[i] >= 0
}

//functia MaxProfitWithJobI intoarce solutia partiala si optima cu job-ul i inclus
method MaxProfitWithJobI(jobs: seq <Job>, i: int, dp: seq<int>, allSol :seq<seq<int>>) returns (maxProfit:int, partialSolution: seq<int>)
  requires validProblem(jobs)
  requires PositiveProfitsDP(dp)
  requires 1 <= i < |jobs|
  requires |allSol| == i
  requires |dp| == i
  requires OptimalPartialSolutions(allSol, jobs, dp, i)
  ensures isPartialSolution(partialSolution, jobs, i + 1)
  ensures maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0)
  ensures partialSolutionWithJobI(partialSolution, jobs, i)
  ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
{

  var max_profit := 0;
  var partialSolutionPrefix : seq<int> := [];
  var j := i - 1;
  var length := 0;

  //cautam un job care nu se suprapune cu i si demonstram ca toate job-urile dintre j si i se suprapun cu i
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

  //assume false;
  if j >= 0 //inseamna ca a gasit un job j cu care nu se suprapune cu i (pe o pozitie >= 0)
  {

    max_profit, partialSolution, length := OptimalPartialSolutionWhenNonOverlapJob(jobs, i, dp, allSol, j);
    //assume false;

  }
  else //nu am gasit niciun job j care sa nu se suprapuna cu i
  {
    //assume false;
    max_profit, partialSolution, length := OptimalPartialSolutionWhenOverlapJob(jobs, i, dp);

  }

  assert isPartialSolution(partialSolution, jobs, length);
  assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit, 0) ;
  maxProfit := max_profit;
  assert maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0);
}

//demonstram ca daca adaugam [0] la o secventa profitul acesteia ramane acelasi ca inainte de adaugare
lemma NotAddingAJobKeepsSameProfit(partialSol: seq<int>, jobs: seq <Job>, index: int)
  requires validJobsSeq(jobs)
  requires 0 <= index <= |partialSol| < |jobs|
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


//o subsecventa a unei solutii partiale este tot solutie partiala
lemma SubSeqOfPartialIsAlsoPartial(partialSol: seq<int>, jobs: seq<Job>, length: int)
  requires length + 1 == |partialSol|
  requires 0 <= length < |jobs|
  requires validJobsSeq(jobs)
  requires isPartialSolution(partialSol, jobs, length + 1)
  ensures isPartialSolution(partialSol[..length], jobs, length)
{

}

//lemma ajutatoare pentru metoda leadsToOptimalWithTakingJobI
//demonstram ca in cazul in care profitul solutiei partiale ce contine job-ul i este mai mare decat dp[i-1] (profitul optim anterior)
//aceasta este optima
lemma optimalPartialSolutionWithJobI(i: int, jobs: seq<Job>, maxProfit: int, dp: seq<int>)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires |dp| == i
  requires 1 <= i < |jobs|
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
      assert partialSol == partialSol[..i] + [0];
      assert PartialSolutionPrefixProfit(partialSol, jobs, 0) == PartialSolutionPrefixProfit(partialSol[..i], jobs, 0);
      SubSeqOfPartialIsAlsoPartial(partialSol, jobs, i);
      assert isPartialSolution(partialSol[..i], jobs, |partialSol[..i]|);
      assert PartialSolutionPrefixProfit(partialSol[..i], jobs, 0) <= dp[i - 1]; //din requires(1)
      assert PartialSolutionPrefixProfit(partialSol, jobs, 0)  <= dp[i - 1];
      assert dp[i - 1] < maxProfit; //care stim din preconditii ca este < maxProfit
      //assume false;
      //assume false;
      assert HasLessProfit(partialSol, jobs, maxProfit, 0);

    }

  }
}

//ramura din metoda principala in care prin alegerea job-ului i se obtine un profit mai bun decat fara acesta
//metoda in care calculam solutia partiala de lungime i = solutia partiala cu job-ul i si demonstram ca aceasta este optima, stiind ca profitul acesteia este > decat dp[i-1]
method leadsToOptimalWithTakingJobI(jobs: seq<Job>, dp:seq<int>, allSol: seq<seq<int>>, i: int, maxProfit: int, partialSolWithJobI: seq<int>) returns (optimalPartialSolution: seq<int>, profits:seq<int>)
  requires validProblem(jobs)
  requires 1 <= i < |jobs|
  requires |dp| == |allSol| == i
  requires isPartialSolution(partialSolWithJobI, jobs, i + 1)
  requires partialSolutionWithJobI(partialSolWithJobI, jobs, i)
  requires maxProfit == PartialSolutionPrefixProfit(partialSolWithJobI, jobs, 0);
  requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
  requires forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i //stim din invariant
  requires dp[i - 1] < maxProfit
  ensures isPartialSolution(optimalPartialSolution, jobs, i + 1)
  ensures |profits| == i + 1
  ensures profits == dp + [maxProfit]
  ensures isOptimalPartialSolution(optimalPartialSolution, jobs, i + 1)
  ensures HasProfit(optimalPartialSolution, jobs, 0, profits[i])
  ensures forall partialSol :: |partialSol| == i + 1  && isPartialSolution(partialSol, jobs, i + 1) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
{
  
  profits := dp + [maxProfit]; //profitul general creste deorece cu job-ul curent se obtine un profit mai mare
  assert partialSolWithJobI[i] == 1;

  optimalPartialSolution := partialSolWithJobI; //solutia contine job-ul i
  assert isPartialSolution(optimalPartialSolution, jobs, i + 1);
  assert PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0) == maxProfit;
  assert partialSolutionWithJobI(optimalPartialSolution, jobs, i);

  //demonstram ca aceasta solutie partiala este si optima
  optimalPartialSolutionWithJobI(i, jobs, maxProfit, dp);

  assert forall partialSol :: |partialSol| == i + 1   && isPartialSolution(partialSol, jobs, i + 1) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
  assert isOptimalPartialSolution(optimalPartialSolution, jobs, i + 1);
}


lemma optimalPartialSolutionWithoutJobI(i: int, jobs: seq<Job>, maxProfit: int, dp: seq<int>, profits: seq<int>)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires 1 <= i < |jobs|
  requires |dp| == i
  requires |profits| == i + 1
  requires profits[i] == dp[i - 1]
  requires dp[i - 1] >= maxProfit
  requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
  requires forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i
  ensures forall partialSol :: |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|) ==> HasLessProfit(partialSol, jobs, profits[i], 0)
{
  forall partialSol | |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|)
    ensures HasLessProfit(partialSol, jobs, profits[i], 0) //profits[i] == dp[i - 1] => imi doresc sa arat ca se obtin profituri <= dp[i-1] si am reusit YEEEE:))
  {
    if partialSol[i] == 1
    {
      //stim ca toate au profitul <= max_profit, iar max_profit <= dp[i-1]
      assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0);
      assert maxProfit <= dp[i - 1];
      assert profits[i] == dp[i - 1];
      assert maxProfit <= profits[i];
      assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
      //assume false;
    }
    else
    {
      //assume false;
      assert partialSol[i] == 0;
      //daca adugam 0 profitul ramane acelasi cu profitul de inainte de a adauga job-ul <= dp[i-1] (pasul anterior) <= dp[i - 1] SMART
      //profitul ramane dp[i-1] care stim ca este optim pentru toate solutiile partiale de lungime i - 1 din invariant
      assert partialSol[..i] + [0] == partialSol;
      NotAddingAJobKeepsSameProfit(partialSol[..i], jobs, 0);
      assert PartialSolutionPrefixProfit(partialSol[..i], jobs, 0) == PartialSolutionPrefixProfit(partialSol, jobs, 0); //<= dp[i-1] IMPORTANT
      assert isPartialSolution(partialSol[..i], jobs, |partialSol[..i]|);
      assert forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0);
      assert PartialSolutionPrefixProfit(partialSol[..i], jobs, 0) <= dp [i - 1]; //dp[i-1] profit optim ..i !!IMPORTANT
      assert PartialSolutionPrefixProfit(partialSol, jobs, 0) <= dp[i - 1];
      assert profits[i] == dp[i - 1];
      assert PartialSolutionPrefixProfit(partialSol, jobs, 0) <= profits[i];
    }
  }
}

//ramura in care prin alegerea job-ului i se obtine un profit <= cu cel anterior (dp[i-1]) si nu se adauga job-ul i la solutia optima
method leadsToOptimalWithoutTakingJobI(jobs: seq<Job>, dp:seq<int>, allSol: seq<seq<int>>, i: int, maxProfit: int, partialSol: seq<int>) returns (optimalPartialSolution: seq<int>, profits:seq<int>)
  requires validProblem(jobs)
  requires 1 <= i < |jobs|
  requires |dp| == |allSol| == i
  requires |partialSol| == i
  requires isOptimalPartialSolution(partialSol, jobs, i)
  requires dp[i - 1] == PartialSolutionPrefixProfit(partialSol, jobs, 0)
  requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0)
  requires forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i
  requires dp[i - 1] >= maxProfit
  ensures isPartialSolution(optimalPartialSolution, jobs, i + 1)
  ensures isOptimalPartialSolution(optimalPartialSolution, jobs, i + 1)
  ensures profits == dp + [dp[i-1]]
  ensures |profits| == i + 1
  ensures HasProfit(optimalPartialSolution, jobs, 0, profits[i])
  ensures forall partialSol :: |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
{
  //demonstram ca dp[i - 1] este maxim folosindu-ne de ce stim de la pasul anterior (toate profiturile posibile <= dp[i-1] )
  //daca nu adaugam un job, profitul ramane acelasi cu cel anterior care este <= dp[i-1] ==> conditia se pastreaza dp[i] = dp[i-1]
  assert dp[i-1] >= maxProfit;

  AssociativityOfProfitFunc(partialSol, jobs, 0, 0);

  profits := dp + [dp[i-1]]; //profitul maxim ramane profitul anterior deoarece prin prin selectarea job-ului curent nu se obtine un profit mai mare
  
  assert dp[i - 1] == PartialSolutionPrefixProfit(partialSol, jobs, 0);
  
  optimalPartialSolution := partialSol + [0]; //solutia nu contine job-ul i deoarece se obtine un profit mai bun fara el 

  assert isPartialSolution(optimalPartialSolution, jobs, i + 1);

  assert profits[i] == PartialSolutionPrefixProfit(optimalPartialSolution, jobs, 0);
  
  assert partialSolutionWithoutJobI(optimalPartialSolution, jobs, i);

  optimalPartialSolutionWithoutJobI(i, jobs, maxProfit, dp, profits);

  assert isOptimalPartialSolution(optimalPartialSolution, jobs, i + 1);
  assert forall partialSol :: |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|) ==> HasLessProfit(partialSol, jobs, profits[i], 0);
}


method WeightedJobScheduling(jobs: seq<Job>) returns (sol: seq<int>, profit : int)
  requires validProblem(jobs)
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
    invariant i == |dp|
    invariant 1 <= |dp| <= |jobs|
    decreases |jobs| - |dp|
    invariant isPartialSolution(solution, jobs, i) 
    invariant |solution| == i 
    invariant i == |allSol| 
    decreases |jobs| - |allSol|
    decreases |jobs| - |allSol[i-1]|
    invariant isPartialSolution(allSol[i-1], jobs, i)
    invariant HasProfit(solution, jobs, 0, dp[i - 1])
    invariant HasProfit(allSol[i - 1], jobs, 0 , dp[i - 1])
    invariant allSol[i - 1] == solution
    invariant OptimalPartialSolutions(allSol, jobs, dp, i)
    invariant isOptimalPartialSolution(allSol[i - 1], jobs, i)   
    invariant forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1], 0) //sol par optima
    invariant forall i :: 0 <= i < |dp| ==> dp[i] >= 0
    invariant isOptimalPartialSolution(solution, jobs, i)
  {
    var maxProfit, partialSolWithI := MaxProfitWithJobI(jobs, i, dp, allSol);

    assert maxProfit == PartialSolutionPrefixProfit(partialSolWithI, jobs, 0);
    assert partialSolutionWithJobI(partialSolWithI, jobs, i);
    assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit, 0);
    //calculeaza maximul dintre excluded profit si included profit
    //maximul dintre profitul obtinut pana la job-ul anterior si profitul obtinut cu adugarea job-ului curent

    if dp[i-1] >= maxProfit //se obtine un profit mai bun fara job-ul curent //lemma requires conditia
    {
      
      solution, dp := leadsToOptimalWithoutTakingJobI(jobs, dp, allSol, i, maxProfit, solution);
      assert isOptimalPartialSolution(solution, jobs, i + 1);

    }
    else //alegem job-ul i dp[i-1] < maxProfit
    {

      solution, dp := leadsToOptimalWithTakingJobI(jobs, dp, allSol, i, maxProfit, partialSolWithI);
      assert isOptimalPartialSolution(solution, jobs, i + 1);

    }
    allSol := allSol + [solution]; //cream secventa de solutii partiale optime(care includ job-ul curent sau nu) pentru fiecare job in parte
    //allSol[j] = contine solutia partiala optima pana la pozitia j inclusiv (formata din job-urile pana la pozitia j inclusiv, partiala optima)
    i := i + 1;
  }

  sol := solution;
  profit := dp[|dp|-1]; //ultimul profit este maxim
}


method Main()
{
  print("Roxana");
  var job1: Job := Tuple(jobStart := 1, jobEnd := 2, profit := 50);
  var job2: Job := Tuple(jobStart := 3, jobEnd := 5, profit := 20);
  var job3: Job := Tuple(jobStart := 6, jobEnd := 19, profit := 100);
  var job4: Job := Tuple(jobStart := 2, jobEnd := 100, profit := 200);
  var jobs: seq<Job> := [job1, job2, job3, job4];
  // //secventa de job-uri trebuie sa fie valida (1)
  // //-----------------------------------contina job-uri diferite din pctdv al cel putin un timp (st sau sf)
  var solutie : seq<int> := [];
  var profit : int := 0;
  solutie, profit := WeightedJobScheduling(jobs);
  // print ("Solutia optima: ", solutie);
  // print ("Profitul maxim pentru secventa de job-uri: ", profit);
  print (solutie);
  print (profit);
  //solutia trebuie sa contina valori 0, 1 , sa fie de lungime |jobs|, job-uri care nu se suprapun si sa fie de profit maxim

}
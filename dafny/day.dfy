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
    j1.jobEnd > j2.jobStart &&  j2.jobEnd > j1.jobStart
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
//ensures forall index :: 0 <= index < |solution| ==> PartialSolutionProfit(solution, jobs, index, firstPosition) == if index == |solution| || (firstPosition + index == |jobs| )  then 0 else solution[index] * jobs[firstPosition + index].profit + PartialSolutionProfit(solution, jobs, index + 1, firstPosition);

{   

    if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionPrefixProfit(solution, jobs, index + 1)
}


predicate hasNoOverlappingJobs(partialSol: seq<int>, jobs: seq<Job>)
requires validJobsSeq(jobs)
{
   |partialSol| <= |jobs|  && forall i, j :: 0 <= i < j < |partialSol| ==>
        (partialSol[i] == 1 && partialSol[j] == 1) ==> !overlappingJobs(jobs[i], jobs[j]) 
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


lemma Add2NotOverlappingSeq0(seq1: seq<int>, jobs: seq<Job>, j : int)
// seq1 == allSol[j] = lungime j + 1 , allSol[0]  = [1], allSol[1] = [1,1];
// seq2 == subSol, unde |subSol|  == i - j + 1
requires validJobsSeq(jobs)
requires 0 <= j < j+1 < |jobs|
requires |seq1| == j + 1 //ultima valoare este pe pozitia j 
requires hasNoOverlappingJobs(seq1, jobs)
requires areOrderedByEnd(seq1, jobs)
ensures hasNoOverlappingJobs(seq1 + [0], jobs)
{

}


lemma AssociativityOfProfitFunc(partialSolPrefix : seq<int>, jobs: seq<Job>, val: int, index: int)
requires 0 <= index <= |partialSolPrefix|
requires validJobsSeq(jobs)
requires 0 <= val <= 1
requires |jobs| >= 1
requires 1 <= |jobs| - |partialSolPrefix| <= |jobs| 
requires 0 <= |partialSolPrefix| < |jobs| 
decreases |partialSolPrefix| - index 
ensures PartialSolutionPrefixProfit(partialSolPrefix, jobs, index) + val * jobs[|partialSolPrefix|].profit == 
 PartialSolutionPrefixProfit(partialSolPrefix + [val], jobs, index)
{
  if |partialSolPrefix| == index {

  }
  else
  {

    // assert PartialSolutionPrefixProfit(partialSolPrefix, jobs, index) == 
    // partialSolPrefix[index] * jobs[index].profit + PartialSolutionPrefixProfit(partialSolPrefix, jobs, index + 1 ); 
    // assert PartialSolutionPrefixProfit
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
requires 0 <= length <= |jobs|
{ 
    isPartialSolution(partialSol, jobs, length) && 
    forall otherSol :: isPartialSolution(otherSol, jobs, length) ==> HasLessProfit(otherSol, jobs, PartialSolutionPrefixProfit(partialSol, jobs, 0))
}

predicate HasProfit(partialSol: seq<int>, jobs: seq <Job>, profit: int )
requires validJobsSeq(jobs) 
requires |jobs| >= 1
requires |partialSol| <= |jobs|
{
    PartialSolutionPrefixProfit(partialSol, jobs, 0) ==  profit
}

ghost predicate isOptimalPartialSolutionDP(partialSol: seq<int>, jobs: seq<Job>, length : int, dp:int)
requires validJobsSeq(jobs) 
requires 1 <= |jobs| 
requires 0 <= length <= |jobs|
{ 
    |partialSol| == length && isOptimalPartialSolution(partialSol, jobs, length) && HasProfit(partialSol, jobs, dp)
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

predicate HasLessProfit(partialSol: seq<int>, jobs: seq<Job>,  maxProfit: int)
requires validJobsSeq(jobs)
requires |partialSol| <= |jobs|
{
    PartialSolutionPrefixProfit(partialSol, jobs, 0) <= maxProfit
}

//inca nedemonstrat max_profit
//functia maxprofit intoarce solutia partiala ce contine job-ul i 
method MaxProfit(jobs: seq <Job>, i: int, dp: seq<int>, allSol :seq<seq<int>>) returns (maxProfit:int, partialSolution: seq<int>)
requires validJobsSeq(jobs)
requires distinctJobsSeq(jobs)
requires sortedByActEnd(jobs)
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
ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, maxProfit) 
{       
       
        var max_profit := 0;
        var partialSolutionPrefix : seq<int> := [];
        var j := i - 1;
        var length := 0;
        //assert  j != -1 ==> max_profit == PartialSolutionProfit(subSol, jobs, 0, j + 1) ;
        while j >= 0 && jobs[j].jobEnd > jobs[i].jobStart //
            // invariant j >= 0 ==> jobs[j].jobStart < jobs[j].jobEnd
            invariant j >= -1 && j < i
            //invariant forall k :: j < k < i ==> jobs[k].jobEnd > jobs[i].jobStart && startsBeforeEnding(jobs[k], jobs[i]) //problema
            //invariant j >= 0 && jobs[j].jobEnd > jobs[i].jobStart ==> overlappingJobs(jobs[j], jobs[i])
            invariant forall k :: j < k < i ==> jobs[k].jobEnd > jobs[i].jobStart 
            invariant forall k :: j < k < i ==> validJob(jobs[k])
            invariant forall k :: j < k < i ==> JobComparator(jobs[k], jobs[i])
            invariant forall k :: j < k < i ==> jobs[k].jobEnd > jobs[k].jobStart
            invariant forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]) //stiu doar despre primul job j(ultima val a while-ului) nu se suprapune cu i 
                {   
                    j := j - 1;            
                } 

        assert  j != -1 ==> !overlappingJobs(jobs[j], jobs[i]);
        assert |partialSolutionPrefix| == length;
        assert hasNoOverlappingJobs(partialSolutionPrefix, jobs);

        if j >= 0
        {  
            //assume false;
            assert !overlappingJobs(jobs[j], jobs[i]);
            assert hasNoOverlappingJobs(allSol[j], jobs); 
            assert HasProfit(allSol[j], jobs, dp[j]);
            assert isOptimalPartialSolution(allSol[j], jobs, |allSol[j]|); 
            //assert forall partialSol :: |partialSol| == j && isPartialSolution (partialSol, jobs, j) ==> HasLessProfit(partialSol, jobs, PartialSolutionPrefixProfit(allSol[j], jobs, 0));
            assert |allSol[j]| == j + 1;
            partialSolutionPrefix := allSol[j];
            assert dp[j] == PartialSolutionPrefixProfit(allSol[j], jobs, 0);
            length := length + |allSol[j]|; 
            assert length == |allSol[j]|;
            assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
            assert hasNoOverlappingJobs(partialSolutionPrefix, jobs);
            max_profit := max_profit + dp[j]; //adaug profitul pt solutia partiala optima (cu job-uri pana la pozitia j)
            var nr_of_zeros := i - |allSol[j]|; // nr de elemente dintre i si j 
            assert |allSol[j]| == j + 1;
            assert length + nr_of_zeros < |jobs|;
            assert nr_of_zeros + |allSol[j]| == i ;  
            while nr_of_zeros > 0 
                decreases nr_of_zeros
                decreases i - length 
                invariant |partialSolutionPrefix| == length
                invariant forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1
                invariant length + nr_of_zeros < |jobs|;
                invariant length + nr_of_zeros <= i;
                invariant length < |jobs|;
                invariant length == i - nr_of_zeros
                invariant nr_of_zeros == 0 ==> length == i 
                invariant hasNoOverlappingJobs(partialSolutionPrefix, jobs)
                invariant forall k :: j < k < |partialSolutionPrefix| ==> partialSolutionPrefix[k] == 0
                invariant max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0)
                    {   
                        AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 0, 0);
                        assert max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0);
                        partialSolutionPrefix :=  partialSolutionPrefix + [0]; //se adauga de nr_of_zeros ori 
                        assert length + nr_of_zeros < |jobs|;
                        length := length + 1;
                        nr_of_zeros := nr_of_zeros - 1;
                        //max_profit := max_profit + 0;
                        //assert PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0) == PartialSolutionPrefixProfit(partialSolutionPrefix + [0], jobs, 0);
                        assert max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0); 
                    }
            //assert nr_of_zeros == 0;
            //assert length == i; //de demonstrat 
            max_profit := max_profit + jobs[i].profit;
            assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit) ;
        } 
        else if j == -1
        {   
            //assume false;  
            //cazul in care punem numai zerouri 
            assert forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]);
            var nr_of_zeros := i; 
            while nr_of_zeros > 0 
                decreases nr_of_zeros
                decreases i - length
                invariant |partialSolutionPrefix| == length
                invariant forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
                invariant length + nr_of_zeros <= i;
                invariant length < |jobs|;
                invariant length == i - nr_of_zeros
                invariant nr_of_zeros == 0 ==> length == i 
                invariant hasNoOverlappingJobs(partialSolutionPrefix, jobs)
                invariant max_profit == PartialSolutionPrefixProfit(partialSolutionPrefix, jobs, 0)
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
            max_profit := max_profit + jobs[i].profit;
            assert partialSolutionWithJobI(partialSolutionPrefix + [1], jobs, i);
            assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit) ;
        }
        assert j == -1 ==> containsOnlyZeros(partialSolutionPrefix);
        assert length == i;
        assert |partialSolutionPrefix| == length;
        assert length < |jobs|;
        assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
        assert hasNoOverlappingJobs(partialSolutionPrefix, jobs);
        AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 1, 0);
        // forall k | 0 <= k < i 
        // ensures partialSolution[k] != 0 ==> !overlappingJobs(jobs[k], jobs[i])
        // {
        //     if j >= 0 //adaug allSol[j]
        //     {
        //         assert !overlappingJobs(jobs[j], jobs[i]);
        //         assert hasNoOverlappingJobs(allSol[j], jobs);
        //         assert forall k :: 0 <= k < |allSol[j]| ==> allSol[j][k] != 0 ==> !overlappingJobs(jobs[k], jobs[i]);

        //     }
        //     else if j == -1 //pun doar zerouri
        //     {   
        //         assert  containsOnlyZeros(partialSolution);
        //         assert  forall p :: 0 <= p < |partialSolution| ==> partialSolution[p] != 0 ==> !overlappingJobs(jobs[p], jobs[i]);
        //     }
        // }
        partialSolution := partialSolutionPrefix + [1]; //includem si job-ul i (solutia partiala ce contine job-ul i)
        length := length + 1;
        //max_profit := max_profit + jobs[i].profit;
        assert max_profit == PartialSolutionPrefixProfit(partialSolution, jobs, 0);
        assert |partialSolution| <= |jobs|; //de demonstrat ca dupa ce adugam job-ul i obtinem o solutie p cu job-uri care nu se suprapune
        assert |partialSolution| == length;
        assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolution[i] <= 1;
        //aici j poate fi -1 sau 0 , daca j = -1 inseamna ca avem numai zerouri in fata lui i , daca nu, avem si allSol[j]
        //stim ca daca avem zerouri nu se suprapun cu i, trebuie sa demonstram ca i nu se suprapune cu allSol[j]
        assert hasNoOverlappingJobs(partialSolution, jobs);
        assert isPartialSolution(partialSolution, jobs, length);
        assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, max_profit) ;
        maxProfit := max_profit;
        assert maxProfit == PartialSolutionPrefixProfit(partialSolution, jobs, 0); 
}

// lemma OneIsBiggerThan0(jobs: seq<Job>)
// requires |jobs| >= 1
// requires validJobsSeq(jobs)
// ensures PartialSolutionPrefixProfit([0], jobs, 0) <= PartialSolutionPrefixProfit([1], jobs, 0);
// { 
//     var profit1 := PartialSolutionPrefixProfit([0], jobs, 0);
//     var profit2 := PartialSolutionPrefixProfit([1], jobs, 0);
//     assert profit1 == 0 ;
//     assert validJob(jobs[0]);
//     assert jobs[0].profit >= 0;
//     assert profit2 >= 0;
//     assert profit1 <= profit2;
// }

// lemma leadsToOptimalWithoutTaking(partialSol: seq<int>, jobs: seq<Job>, length: int)
// ensures isOptimalPartialSolution(partialSol, jobs, length)
// {

// }

// lemma leadsToOptimalWithTaking(partialSol: seq<int>, jobs: seq<Job>, length: int)
// ensures isOptimalPartialSolution(partialSol, jobs, length)
// {

// }
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


method WeightedJobScheduling(jobs: seq<Job>) returns (sol: seq<int>, profit : int)
    requires |jobs| >= 1
    requires validJobsSeq(jobs)
    requires distinctJobsSeq(jobs)
    requires sortedByActEnd(jobs)
    ensures isSolution(sol, jobs)
    ensures isOptimalSolution(sol, jobs)
{   
    var dp :seq<int> := [];
    var dp0 := jobs[0].profit; //dynamic programming
    dp := dp + [dp0]; 
    var solution : seq<int> := [1];
    var i: int := 1;
    var allSol : seq<seq<int>> := [];
    allSol := allSol + [[1]]; //adaugam solutia pana la primul job inclusiv 
    assert |solution| == 1;
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
        invariant i == |allSol|
        decreases |jobs| - |allSol|
        invariant |allSol[i-1]| == i 
        invariant forall k :: 0 <= k < i ==> |allSol[k]| == k + 1
        invariant 1 <= |allSol[i-1]| <= |jobs|
        decreases |jobs| - |allSol[i-1]| 
        invariant isPartialSolution(allSol[i-1], jobs, i)
        invariant ValidPartialSolutions(allSol, jobs, i) //i = 1, allSol are lungime 1 , deci doar AllSol[0] exista 
        invariant dp[i-1] == PartialSolutionPrefixProfit(solution, jobs, 0)
        invariant dp[i-1] == PartialSolutionPrefixProfit(allSol[i-1], jobs, 0)
        invariant OptimalPartialSolutions(allSol, jobs, dp, i)
        invariant isOptimalPartialSolution(allSol[i - 1], jobs, i)
        invariant partialSolutionWithoutJobI(solution, jobs, i - 1) ==> PartialSolutionPrefixProfit(solution, jobs, 0) == PartialSolutionPrefixProfit(solution[..|solution|- 1], jobs, 0)
        // invariant partialSolutionWithoutJobI(solution, jobs, i - 1) ==> HasLessProfit(solution, jobs, dp[i-1])
        // invariant partialSolutionWithJobI(solution, jobs, i - 1) ==> HasLessProfit(solution, jobs, dp[i-1])
        //invariant HasLessProfit(solution, jobs, dp[i-1]);
        invariant forall partialSol :: |partialSol| == i  && isPartialSolution(partialSol, jobs, i) ==> HasLessProfit(partialSol, jobs, dp[i - 1]);
        invariant isOptimalPartialSolution(solution, jobs, i)
    {  
        //castigul pt sol partiala este dp
        var maxProfit, solForCurrentJobIncluded := MaxProfit(jobs, i, dp, allSol); 

        //calculeaza maximul dintre excluded profit si included profit 
        //maximul dintre profitul obtinut pana la job-ul anterior si profitul obtinut cu adugarea job-ului curent  
        
        if dp[i-1] >= maxProfit //se obtine un profit mai bun fara job-ul curent //lemma requires conditia
        {   
            //assume forall k :: 0 <= k < i ==> |allSol[k]| == k + 1;
            //assume false;
            //assert dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0);
            //daca nu adaugam un job, profitul ramane acelasi cu cel anterior care este <= dp[i-1] ==> conditia se pastreaza dp[i] = dp[i-1]
            AssociativityOfProfitFunc(solution, jobs, 0, 0);
            dp := dp + [dp[i-1]]; //profitul maxim ramane profitul anterior deoarece prin prin selectarea job-ului curent nu se obtine un profit mai mare  
            //leadsToOptimalWithoutTaking(solution, jobs, i + 1);
            assert |solution| < |jobs|;
            NotAddingAJobKeepsSameProfit(solution, jobs, 0);
            solution := solution + [0]; //solutia nu contine job-ul i 
            assert isPartialSolution(solution, jobs, i + 1);
            assert dp[i] == PartialSolutionPrefixProfit(solution, jobs, 0);
            assert partialSolutionWithoutJobI(solution, jobs, i);
            //assert  partialSolutionWithoutJobI(solution, jobs, i) ==> PartialSolutionPrefixProfit(solution, jobs, 0) == PartialSolutionPrefixProfit(solution[..|solution|- 1], jobs, 0);
            // forall partialSol | isPartialSolution(partialSol, jobs, |partialSol|) && partialSolutionWithoutJobI(partialSol, jobs, i)
            // ensures PartialSolutionPrefixProfit(solution, jobs, 0) <= dp[i]
            // {

            // }
            //assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithoutJobI(partialSol, jobs, i) ==> PartialSolutionPrefixProfit(solution, jobs, 0) == PartialSolutionPrefixProfit(solution[..|solution|- 1], jobs, 0);
            assume isOptimalPartialSolution(solution, jobs, i + 1);
        }
        else //alegem job-ul i 
        {   
            assume forall k :: 0 <= k < i ==> |allSol[k]| == k + 1;
            //assert dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i);
            dp := dp + [maxProfit]; //profitul general creste deorece cu job-ul curent se obtine un profit mai mare 
            //leadsToOptimalWithTaking(solution, jobs, i + 1);
            assert solForCurrentJobIncluded[i] == 1;
            solution := solForCurrentJobIncluded; //solutia contine job-ul i 
            assert isPartialSolution(solution, jobs, i + 1);
            assert dp[i] == PartialSolutionPrefixProfit(solution, jobs, 0);
            assert partialSolutionWithJobI(solution, jobs, i);
            //stim din functia max_profit ca aceasta solutie ce contine job-ul i este solutia optima (cu job-ul i)
            //assert PartialSolutionPrefixProfit(solution, jobs, 0) == maxProfit;
            //assert PartialSolutionPrefixProfit(solution, jobs, 0) == dp[i];
            assert isPartialSolution(solution, jobs, i + 1);
            assert  solution[i] == 1;
            forall partialSol | |partialSol| == i + 1 && isPartialSolution(partialSol, jobs, |partialSol|)
            ensures HasLessProfit(partialSol, jobs, maxProfit);
            {
                if partialSol[i] == 1
                {
                    // assume false;
                    //demonstrat din functia MaxProfit 
                }
                else{
                     //daca nu adaug un job profitul ramane <= dp[i-1] (invariant sulutie partiala optima), care in aceasta ramura a if-ului este <= max_profit 
                     // ==> tranzitivitate ==> profitul curent <= dp[i] (= max_profit)
                     assume false;
                     NotAddingAJobKeepsSameProfit(partialSol[..i], jobs, 0);
                     assert partialSol[..i] + [0] == partialSol;
                     assert PartialSolutionPrefixProfit(partialSol[..i], jobs, 0) == PartialSolutionPrefixProfit(partialSol, jobs, 0);
                     assert PartialSolutionPrefixProfit(allSol[i - 1], jobs, 0) == dp[i - 1];
                     assert isOptimalPartialSolution(allSol[i - 1], jobs, |allSol[i - 1]|);
                     assert isPartialSolution(partialSol[..i], jobs, |partialSol[..i]|);
                     assert dp[i - 1] >= PartialSolutionPrefixProfit(partialSol[..i], jobs, 0);
                     assert dp[i - 1] < maxProfit;
                     //assume false;

                }
            
            }
            assert maxProfit == dp[i];
            // forall partialSol | |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i)
            // ensures HasLessProfit(partialSol, jobs, dp[i]);
            // {
            //     assert isPartialSolution(solution, jobs, i + 1);
            //     assert  solution[i] == 1;
            // }
            // assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> PartialSolutionPrefixProfit(partialSol, jobs, 0) <= dp[i];
            assert forall partialSol :: |partialSol| == i + 1   && isPartialSolution(partialSol, jobs, i + 1) ==> HasLessProfit(partialSol, jobs, dp[i]);
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
    profit := dp[|dp|-1];
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
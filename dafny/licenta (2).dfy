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

predicate notOverlappingJobs(jobs:seq<Job>, j: int, i: int)
requires 0 <= j < i < |jobs|
requires validJob(jobs[i])
requires validJob(jobs[j])
{
    !overlappingJobs(jobs[j], jobs[i])
}

predicate overlappingJobs(j1:Job, j2:Job)
requires validJob(j1)
requires validJob(j2)
{
    j1.jobEnd > j2.jobStart &&  j2.jobEnd > j1.jobStart  // nu se suprapun 
    //primul job se termina inainte ca al 2-lea sa inceapa (j1, j2), si primul job incepe inainte ca al 2-lea sa se termine (j2, j1)
    //ele fiind deja ordonate dupa timpul de finish 
}

predicate disjointJobsSeq(j1:Job, j2:Job)
requires validJob(j1)
requires validJob(j2)
{
    differentJobs(j1, j2) && !overlappingJobs(j1, j2)
}

predicate sortedByActEnd(s: seq<Job>)
    requires validJobsSeq(s)
{
    forall i, j :: 0 <= i < j < |s| ==> JobComparator(s[i], s[j])
}

function Max(a: int, b: int): int
{
    if a >= b then a else b
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

// function PartialSolutionProfit(solution: seq<int>, jobs: seq<Job>, index: int, length: int): int
// requires |solution| == length
// requires 0 <= index <= |solution|
// // requires 0 <= index <= length
// requires 0 <= length <= |jobs|
// requires 0 <= |solution|
// decreases |solution| - index 
// ensures PartialSolutionProfit(solution, jobs, index, length) == if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionProfit(solution, jobs, index + 1, length)
// {   

//     if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionProfit(solution, jobs, index + 1, length)
// }

// function PartialSolutionProfit(solution: seq<int>, jobs: seq<Job>, index: int, length: int): int //Intrebarea 3: Sa renunt definitiv la functia aceasta si sa inlocuiesc peste tot cu PartialSolutionProfit ?
// requires |solution| == length
// requires 0 <= index <= |solution|
// requires validJobsSeq(jobs)
// requires |jobs| >= 1 //este in regula sau nu ? (Intrebarea 1)
// // requires 0 <= index <= length
// requires 0 <= length <= |jobs|
// requires 0 <= |solution|
// decreases |solution| - index 
// ensures PartialSolutionProfit(solution, jobs, index, length) == PartialSolutionProfit(solution, jobs, 0, 0, length)
// {   
//     PartialSolutionProfit(solution, jobs, 0, 0, length)
    
// }

function PartialSolutionProfit(solution: seq<int>, jobs: seq<Job>, index: int, firstPosition: int,  length: int): int
requires |solution| == length
requires 0 <= index <= |solution|
requires 0 <= index <= length
requires 0 <= length <= |jobs|
requires 0 <= |solution|
requires 0 <= firstPosition <= |jobs| - index
// requires |jobs| - firstPosition > 0             
requires 0 <= firstPosition < |jobs| //daca pun <= |jobs| nu mai trebuie |jobs| >= 1 la PartialSolutionProfit
requires 0 <= firstPosition + index <= |jobs|
decreases |solution| - index 
decreases |jobs| - index
ensures PartialSolutionProfit(solution, jobs, index, firstPosition, length) == if index == |solution| || (firstPosition + index == |jobs|) then 0 else solution[index] * jobs[firstPosition + index].profit + PartialSolutionProfit(solution, jobs, index + 1,firstPosition , length)
{   

    if index == |solution| || (firstPosition + index == |jobs| )  then 0 else solution[index] * jobs[firstPosition + index].profit + PartialSolutionProfit(solution, jobs, index + 1, firstPosition, length)
}



predicate hasNoOverlappingJobs(partialSol: seq<int>, jobs: seq<Job>)
requires validJobsSeq(jobs)
{
   |partialSol| <= |jobs|  && forall i, j :: 0 <= i < j < |partialSol| ==>
        (partialSol[i] == 1 && partialSol[j] == 1) ==> !overlappingJobs(jobs[i], jobs[j]) 
    //!overlappingJobs asigura si ca job-uri sunt diferite 
}

predicate hasNoOverlappingJobs2(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
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

lemma Add2NotOverlappingSeq(seq1: seq<int>, seq2 : seq<int>, jobs: seq<Job>, i : int, j : int)
// seq1 == allSol[j] = lungime j + 1 , allSol[0]  = [1], allSol[1] = [1,1];
// seq2 == subSol, unde |subSol|  == i - j + 1
requires validJobsSeq(jobs)
requires 0 <= j < i < |jobs|
requires i - j == |seq2| //prima valoare este pe pozitia j + 1 
requires |seq1| == j + 1 //ultima valoare este pe pozitia j 
requires |seq1| + |seq2| == i + 1
requires |seq1| + |seq2| <= |jobs|
requires hasNoOverlappingJobs(seq1, jobs)
requires hasNoOverlappingJobs2(seq2, jobs, i, j + 1)
requires jobs[|seq1| - 1].jobEnd <= jobs[i].jobStart //asta stim din if 
requires !overlappingJobs(jobs[j], jobs[i])
requires forall k :: 0 <= k < |seq1| ==> !overlappingJobs(jobs[k], jobs[i])
requires areOrderedByEnd2(seq2, jobs, i, j + 1)
requires areOrderedByEnd(seq1, jobs)
requires forall k :: 0 <= k < |seq2| - 1 ==> seq2[k] == 0 //seq2 este de forma 0...0
//iar seq2 este format dintr-o secventa de job-uri ordonate dupa timpul de sf + care nu se suprapun 
ensures hasNoOverlappingJobs(seq1 + seq2, jobs)
{
    if ( j + 1 < i) {
        var seq1' := seq1 + [0];
        var seq2' := seq2[1..];
        assert seq1 + seq2 == seq1' + seq2';
    } 
    else
    {
        
    }

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

//Inca nedemonstrata, cum as putea face asta ? (*Intrebarea 2)
// lemma Add0ToSolHasSameProfit(partialSol : seq<int>, jobs: seq<Job>, profit:int, length: int)
// requires validJobsSeq(jobs)
// requires |jobs| >= 1
// requires length <= |jobs|
// requires |partialSol| == length
// requires profit == PartialSolutionProfit(partialSol, jobs, 0, 0, length)
// ensures length < |jobs| ==> profit == PartialSolutionProfit(partialSol + [0], jobs, 0, 0, length + 1)
// {
//     if (length + 1 <= |jobs|){ 
//         var seq1' := partialSol + [0]; 
//         var length' := length + 1;
//         assert length' == |seq1'|;
//         var profit' := PartialSolutionProfit(seq1', jobs, 0, 0, length');
//         assert profit == profit';
//         //assume profit == profit';
//         }
//     else
//     {

//     }
// }
// lemma Aux(partialSol: seq<int>, length: int)
// requires length == |partialSol|
// ensures |partialSol[..(length - 1)]| == length - 1
// {

// }


lemma Add0ToSolHasSameProfit2(partialSol : seq<int>, jobs: seq<Job>, profit:int, firstPosition:int, length: int)
// decreases firstPosition
decreases length
requires validJobsSeq(jobs)
requires |jobs| >= 1
requires 1 <= firstPosition < |jobs|
requires 0 <= length < |jobs|
requires |partialSol| == length
//requires length == 0 ==> profit == PartialSolutionProfit(partialSol, jobs, 0, firstPosition, length)
requires length >= 0 ==> profit == PartialSolutionProfit(partialSol, jobs, 0, firstPosition, length)
ensures length >= 0 && firstPosition >= 1==> profit == PartialSolutionProfit([0] + partialSol, jobs, 0, firstPosition - 1,  length + 1)
//ensures length == 1 && firstPosition >= 1 ==> profit == PartialSolutionProfit([0] + partialSol, jobs, 0, firstPosition - 1, length + 1)
//ensures  length >= 1 && firstPosition >= 1 ==> profit == PartialSolutionProfit([0] + partialSol, jobs, 0, firstPosition - 1,  length + 1)
//ensures length == 1 && firstPosition == 0 ==> profit == PartialSolutionProfit([0] + partialSol, jobs, 0, 0, length + 1)
{   
    //if (length + 1 <= |jobs|)
    if (length == 0 && firstPosition >= 1)
    {   
        //assert 
        assert |partialSol| == length;
        assert length == 0;
        var profit' := PartialSolutionProfit([0] + partialSol, jobs, 0, firstPosition - 1,  length + 1);
        assert profit == profit';
    }   
     else  if (length >= 1 && firstPosition >= 1)
    { 
            // var profit' := PartialSolutionProfit([0] + partialSol, jobs, 0, 0,  length + 1);
            // assert profit == profit';
                var lengthh := length - 1;
                assert lengthh == |partialSol[..(length-1)]|;
                var profitt := PartialSolutionProfit(partialSol[..(length - 1)], jobs, 0, firstPosition, lengthh);
                var profit' := PartialSolutionProfit([0] + partialSol[..(length - 1)], jobs, 0, firstPosition - 1, lengthh + 1);
                Add0ToSolHasSameProfit2(partialSol[..(length - 1)], jobs, profitt, firstPosition, lengthh);
                assert  profitt == profit';
                assert [0] + partialSol[..(length - 1)] + [partialSol[length-1]] == [0] + partialSol;
                var profit'' := PartialSolutionProfit([0] + partialSol, jobs, 0, firstPosition - 1 ,  length + 1);
                Add0ToSolHasSameProfit2(partialSol[..(length - 1)], jobs, profitt, firstPosition, lengthh);
                assert [0] + partialSol[..(length - 1)] + [partialSol[length-1]] == [0] + partialSol;
                assert |[0] + partialSol[..(length - 1)] + [partialSol[length - 1]]| == length + 1;
                //var profit'' := PartialSolutionProfit([0] + partialSol[..(length - 1)] + [partialSol[length - 1]], jobs, 0, firstPosition - 1 ,  length + 1);
                assert profit == profit'';
    }
    // else if (length > 1 && firstPosition >= 1)
    // {
    //             // var profit' := PartialSolutionProfit([0] + partialSol, jobs, 0, firstPosition - 1,  length + 1);
    //             // assert profit == profit';
    //             var lengthh := length - 1;
    //             assert lengthh == |partialSol[..(length-1)]|;
    //             var profitt := PartialSolutionProfit(partialSol[..(length - 1)], jobs, 0, firstPosition, lengthh);
    //             var profit' := PartialSolutionProfit([0] + partialSol[..(length - 1)], jobs, 0, firstPosition - 1, lengthh + 1);
    //             Add0ToSolHasSameProfit2(partialSol[..(length - 1)], jobs, profitt, firstPosition, lengthh);
    //             assert  profitt == profit';
    //             assert [0] + partialSol[..(length - 1)] + [partialSol[length-1]] == [0] + partialSol;
    //             var profit'' := PartialSolutionProfit([0] + partialSol, jobs, 0, firstPosition - 1,  length + 1);
    //             assert profit == profit'';
    // }
            
            //var partialSol' := partialSol[..(length - 1)];
            //var profit' := PartialSolutionProfit(partialSol', jobs, 0, firstPosition, length - 1);
            // var partialSol' := partialSol[1..];
            // var profit' := PartialSolutionProfit(partialSol', jobs, 0, 1, length - 1);
            // Add0ToSolHasSameProfit2(partialSol', jobs, profit',  1, length - 1);
            // assert profit == PartialSolutionProfit([0] + partialSol, jobs, 0, firstPosition - 1,  length + 1);
            
            //Add0ToSolHasSameProfit2(partialSol, jobs, profit,  firstPosition, length);
            // var seq1' := [0] + partialSol; 
            // var length'' := length + 1;
            // var firstPosition' := firstPosition - 1;
            // var profit'' := PartialSolutionProfit(seq1', jobs, 0, firstPosition', length'');
            // assert profit'' == profit;

            //Add0ToSolHasSameProfit2(seq1', jobs, profit,  firstPosition', length');
            // var lengthh := length - 1;
            // assert lengthh == |partialSol[..(length-1)]|;
            // var profitt := PartialSolutionProfit(partialSol[..(length - 1)], jobs, 0, firstPosition, lengthh);
            // var profit' := PartialSolutionProfit([0] + partialSol[..(length - 1)], jobs, 0, firstPosition - 1, lengthh + 1);
            // Add0ToSolHasSameProfit2(partialSol[..(length - 1)], jobs, profitt, firstPosition, lengthh);
            // assert  profitt == profit';

}

predicate isPartialSolution(partialSol: seq<int>, jobs: seq<Job>, index: int)
requires validJobsSeq(jobs)
{   //job-urile din solutia partiala nu trebuie sa se suprapuna 
    |partialSol| == index &&
    forall i :: 0 <= i <= |partialSol| - 1 ==> (0 <= partialSol[i] <= 1) && hasNoOverlappingJobs(partialSol, jobs)
}


predicate ValidPartialSolutions(allSol:seq<seq<int>>, jobs: seq<Job>,  index: int)
requires validJobsSeq(jobs)
{   
    |allSol| == index && forall i : int :: 0 <= i < index ==> isPartialSolution(allSol[i], jobs, i + 1) //pana la i + 1 inseamna pana la 2 -> 0 1 

}


ghost predicate isOptimalPartialSolution(solution: seq<int>, jobs: seq<Job>, length : int)
requires validJobsSeq(jobs) 
requires |jobs| >= 1
requires 0 <= length <= |jobs|
{ 
    isPartialSolution(solution, jobs, length) && 
    forall otherSol :: isPartialSolution(otherSol, jobs, length) ==>  PartialSolutionProfit(solution, jobs, 0, 0, length) >=  PartialSolutionProfit(otherSol, jobs, 0, 0, length)
}

predicate isOptimalPartialSolutionDP(solution: seq<int>, jobs: seq<Job>, length : int, dp:int)
requires validJobsSeq(jobs) 
requires |jobs| >= 1
requires 0 <= length <= |jobs|
{ 
    isPartialSolution(solution, jobs, length) && PartialSolutionProfit(solution, jobs, 0, 0,  length) ==  dp
}

predicate OptimalPartialSolutions(allSol: seq<seq<int>>, jobs: seq<Job>, dp:seq<int>, index: int)
requires validJobsSeq(jobs)
requires index <= |jobs|
{
    |allSol| == index && |dp| == index && forall i : int :: 0 <= i < index ==> isOptimalPartialSolutionDP(allSol[i], jobs, i + 1, dp[i]) 
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
    forall otherSol :: isSolution(otherSol, jobs) ==>  PartialSolutionProfit(solution, jobs, 0, 0, |solution|) >=  PartialSolutionProfit(otherSol, jobs, 0, 0,  |solution|)
}

predicate isOptimalSolutionDP(solution: seq<int>, jobs: seq<Job>, dp: int)
requires validJobsSeq(jobs) 
requires |solution| == |jobs|
{ 
    isSolution(solution, jobs) && SolutionProfit(solution, jobs, 0) == dp
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
requires OptimalPartialSolutions(allSol, jobs, dp, i)
//requires ValidPartialSolutions(allSol, jobs, i) //cerem ca all sol sa contina doar secvente de 0 si 1 si pentru toate 0 <= j < i allSol[j] == j + 1
ensures isPartialSolution(partialSolution, jobs, i + 1)
//aici nu obtinem solutia partiala optima de lungime i+1
//ensures maxProfit == PartialSolutionProfit(partialSolution, jobs, 0, 0, i + 1)
//ensures  maxProfit == PartialSolutionProfit(partialSolution, jobs, 0, 0, i + 1)
{       
       
        var max_profit := jobs[i].profit;
        var subSol := [1];
        var j := i - 1;
        var length := 1;
        while j >= 0
            invariant -1 <= j <= i - 1
            decreases j
            decreases  i - |subSol| 
            invariant 1 <= length <= i + 1
            decreases i - length
            invariant length == i - j 
            invariant i - j == |subSol|
            invariant hasNoOverlappingJobs2(subSol, jobs, i, j + 1)
            invariant areOrderedByEnd2(subSol, jobs, i, j + 1)
            invariant j < |allSol|
            invariant j >= 0 ==> |allSol[j]| == j + 1
            invariant j >= 0 ==> isPartialSolution(allSol[j], jobs, j + 1)
            invariant |subSol| == length
            invariant forall i :: 0 <= i <= length - 1 ==> 0 <= subSol[i] <= 1
            invariant j != -1 ==> forall k :: 0 <= k < |subSol| - 1 ==> subSol[k] == 0
            //invariant max_profit == PartialSolutionProfit(subSol, jobs, 0, j + 1, length) 
            //invariant j == -1 ==> max_profit == PartialSolutionProfit(subSol, jobs, 0, length) 

        {   
            //job-ul j poate sa se termine la ora la care job-ul i incepe 
            if (jobs[j].jobEnd <= jobs[i].jobStart && j < |dp| && j < |allSol|) {

                //assert max_profit == PartialSolutionProfit(subSol, jobs, 0, j + 1, length);
                assert dp[j] == PartialSolutionProfit(allSol[j], jobs, 0, 0, j + 1);
                max_profit := max_profit + dp[j];
                assert |subSol| == length;
                ghost var length' := length;
                assert forall i :: 0 <= i <= length' - 1  ==> 0 <= subSol[i] <= 1;
                assert  hasNoOverlappingJobs2(subSol, jobs, i, j+1); //verificam de la pozitia j+1 pana la i, asa se formeaza subSol i 
                assert hasNoOverlappingJobs(allSol[j], jobs); 
                length := length + |allSol[j]|;
                Add2NotOverlappingSeq(allSol[j], subSol, jobs, i, j);
                subSol := allSol[j] + subSol;
                assert |subSol| == length;
                assert forall i :: 0 <= i <= length - 1 ==> 0 <= subSol[i] <= 1;
                assert hasNoOverlappingJobs(subSol, jobs);
                j := 0;
                //assert max_profit == PartialSolutionProfit(subSol, jobs, 0, j, length);
                //assume max_profit == PartialSolutionProfit(subSol, jobs, 0, j, length);
                //assume max_profit == PartialSolutionProfit(subSol, jobs, 0, length);
                //assume isPartialSolution(subSol, jobs, |subSol|);
            }
            else
            {   
                //assert max_profit == PartialSolutionProfit(subSol, jobs, 0, j + 1, length);
                //assume max_profit == PartialSolutionProfit(subSol, jobs, 0, j, length);
                assert forall m :: 0 <= m < |subSol| - 1  ==> subSol[m] == 0;
                //Add0ToSolHasSameProfit2(subSol, jobs, max_profit, j + 1, length);
                length := length + 1;
                subSol := [0] + subSol; //as adauga i zerouri de ex pt i = 1 adaug 1, pt i = 2 adaug 2 (pozitiile 1, 0 verific)  
                assert forall i :: 0 <= i <= length - 1 ==> 0 <= subSol[i] <= 1;
                assert hasNoOverlappingJobs2(subSol, jobs, i, j);
                max_profit := max_profit + 0 ;
                //assert max_profit == PartialSolutionProfit(subSol, jobs, 0, j, length);
                assert max_profit == PartialSolutionProfit(subSol, jobs, 0, j, length);
            }
            j := j - 1;
            //assume max_profit == PartialSolutionProfit(subSol, jobs, 0, length);
            
        } 
        
        //subSol este solutia partiala ce contine job-ul i 
        maxProfit := max_profit;
        partialSolution := subSol;
        assert |partialSolution| == length;
        assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolution[i] <= 1;
        assert hasNoOverlappingJobs(partialSolution, jobs);
        assert isPartialSolution(partialSolution, jobs, length);
        //assert max_profit == PartialSolutionProfit(subSol, jobs, 0, j + 1, length);
        assert maxProfit == PartialSolutionProfit(partialSolution, jobs, 0, 0, i + 1);
        //assert maxProfit == PartialSolutionProfit(partialSolution, jobs, 0, i + 1);
        ///abia la sf pot demonstra ca solution este solutie partiala deoarece solutia este ordonata conform cu secventa de job-uri

        
}

method WeightedJobScheduling(jobs: seq<Job>) returns (sol: seq<int>, profit : int)
    requires |jobs| >= 1
    requires validJobsSeq(jobs)
    requires distinctJobsSeq(jobs)
    requires sortedByActEnd(jobs)
    ensures isSolution(sol, jobs)
    //ensures isOptimalSolution(sol, jobs)
    //ensures profit == SolutionProfit(sol, jobs, 0)

{   
    var dp :seq<int> := [];
    var dp0 := jobs[0].profit; //dynamic programming
    dp := dp + [dp0]; 
    var solution : seq<int> := [1];
    var i: int := 1;
    var allSol : seq<seq<int>> := [];
    allSol := allSol + [[1]]; //adaugam solutia pana la primul job inclusiv 
    //assume isOptimalPartialSolution(solution, jobs, i);
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
        invariant 1 <= |allSol[i-1]| <= |jobs|
        decreases |jobs| - |allSol[i-1]| 
        invariant isPartialSolution(allSol[i-1], jobs, i)
        invariant ValidPartialSolutions(allSol, jobs, i) //i = 1, allSol are lungime 1 , deci doar AllSol[0] exista 
        //invariant dp[i-1] == PartialSolutionProfit(solution, jobs, 0, 0, i)
        //invariant dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i)
        //invariant OptimalPartialSolutions(allSol, jobs, dp, i)
        //invariant isOptimalPartialSolution(solution, jobs, i)
    {  
        //castigul pt sol partiala este dp
        var maxProfit, solForCurrentJobIncluded := MaxProfit(jobs, i, dp, allSol); 

        //calculeaza maximul dintre excluded profit si included profit 
        //maximul dintre profitul obtinut pana la job-ul anterior si profitul obtinut cu adugarea job-ului curent  
        
        if dp[i-1] >= maxProfit //se obtine un profit mai bun fara job-ul curent 
        {   
            //assert dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i);
            dp := dp + [dp[i-1]]; //profitul general ramane profitul anterior deoarece prin prin selectarea job-ului curent nu se obtine un profit mai mare  
            //Add0ToSolHasSameProfit(solution, jobs, dp[i-1], i);
            solution := solution + [0]; //solutia nu contine job-ul i 
            assert isPartialSolution(solution, jobs, i + 1);
            assert dp[i] == PartialSolutionProfit(solution, jobs, 0, 0, i + 1); //==>adaug 0 profitul ramane acelasi 
            //assume dp[i] == PartialSolutionProfit(solution, jobs, 0, i + 1);
            //assume isOptimalPartialSolution(solution, jobs, i + 1);
        }
        else 
        {   
            //assert dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i);
            dp := dp + [maxProfit]; //profitul general creste deorece cu job-ul curent se obtine un profit mai mare 
            solution := solForCurrentJobIncluded; //solutia contine job-ul i 
            assert isPartialSolution(solution, jobs, i + 1);
            assert dp[i] == PartialSolutionProfit(solution, jobs, 0, 0, i + 1);
            //assume isOptimalPartialSolution(solution, jobs, i + 1);
            
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
    var profit : int :=  PartialSolutionProfit(partial, jobs, 0, 1, 3);
    var profit' : int :=  PartialSolutionProfit(partial', jobs, 0, 0, 4);
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
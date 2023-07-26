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

predicate  differentJobs(j1: Job, j2: Job) //job-uri sunt diferie 
requires validJob(j1) && validJob(j2)
{
    j1.jobStart != j2.jobStart || j1.jobEnd != j2.jobEnd
}

predicate distinctJobsSeq(s: seq<Job>) //predicat pentru toata secventa care se asigura ca job-urile sunt diferite 
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

// function JobProfit(solution: seq<int>, jobs: seq<Job>, index: int): int
// requires 0 <= index < |solution|
// requires 0 <= index < |jobs|
// ensures JobProfit(solution, jobs, index) == solution[index] * jobs[index].profit
// {
//     solution[index] * jobs[index].profit
// }

//am nevoie de o functie profit pentru solutii partiala 

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

function PartialSolutionProfit(solution: seq<int>, jobs: seq<Job>, index: int, length: int): int
requires |solution| == length
requires 0 <= index <= |solution|
// requires 0 <= index <= length
requires 0 <= length <= |jobs|
requires 0 <= |solution|
decreases |solution| - index 
ensures PartialSolutionProfit(solution, jobs, index, length) == if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionProfit(solution, jobs, index + 1, length)
{   

    if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolutionProfit(solution, jobs, index + 1, length)
}

function PartialSolutionProfit2(solution: seq<int>, jobs: seq<Job>, index: int, firstPosition: int,  length: int): int
requires |solution| == length
requires 0 <= index <= |solution|
requires 0 <= index <= length
requires 0 <= length <= |jobs|
requires 0 <= |solution|
requires 0 <= firstPosition <= |jobs| - index
// requires |jobs| - firstPosition > 0             
requires 0 <= firstPosition < |jobs|
requires 0 <= firstPosition + index <= |jobs|
decreases |solution| - index 
decreases |jobs| - index
ensures PartialSolutionProfit2(solution, jobs, index, firstPosition, length) == if index == |solution| || (firstPosition + index == |jobs|) then 0 else solution[index] * jobs[firstPosition + index].profit + PartialSolutionProfit2(solution, jobs, index + 1,firstPosition , length)
{   

    if index == |solution| || (firstPosition + index == |jobs| )  then 0 else solution[index] * jobs[firstPosition + index].profit + PartialSolutionProfit2(solution, jobs, index + 1, firstPosition, length)
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
requires forall k :: 0 <= k < |seq1| ==> !overlappingJobs(jobs[k], jobs[i]);
//requires seq1[|seq1|-1] == 1 && seq2[0] == 1 ==> jobs[|seq1| - 1].jobEnd <= jobs[|seq1|].jobStart 
//asta trebuie sa se intample ca sa poate fi adevarat ca secventa ce se obtine din concatenare este !overlapp
//seq2 trebuie sa fie formata din job-uri ordonate dupa timpul de sf 
//dc ultimul job din prima secventa si cu primul din a2-a secventa nu se suprapun + ambele sunt secv care nu se suprapun ==> seq1 + seq2 nu se suprapun
requires areOrderedByEnd2(seq2, jobs, i, j + 1)
requires areOrderedByEnd(seq1, jobs)
requires forall k :: 0 <= k < |seq2| - 1 ==> seq2[k] == 0 //seq2 este de forma 0...01
//daca ultimul job din seq1 se termina inainte ca ultimul job din seq2 sa inceapa 
//iar seq2 este format dintr-o secventa de job-uri ordonate dupa timpul de sf + care nu se suprapun 
ensures hasNoOverlappingJobs(seq1 + seq2, jobs)
//daca ultimul din seq1 nu se suprapune cu ultimul din seq2, inseamna ca niciunul din seq1 (ordonate dupa sf) nu se suprapune cu ultimul din seq2
//stim ca seq2 este de forma 0001 si trebuie sa ne ocupam doar de ultimul job din seq2 
{
    if ( j + 1 < i) {
        var seq1' := seq1 + [0];
        var seq2' := seq2[1..];
        //assert seq1 + seq2 == seq1' + seq2';
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

predicate isPartialSolution(partialSol: seq<int>, jobs: seq<Job>, index: int)
requires validJobsSeq(jobs)
{   //job-urile din solutia partiala nu trebuie sa se suprapuna 
    |partialSol| == index &&
    forall i :: 0 <= i <= |partialSol| - 1 ==> (0 <= partialSol[i] <= 1) && hasNoOverlappingJobs(partialSol, jobs)
}


// function reverseSeq(inputSeq: seq<int>) : seq<int>
// ensures |inputSeq| == |reverseSeq(inputSeq)| //are aceeasi lungime 
// //ensures forall i :: 0 <= i < |inputSeq| ==> inputSeq[i] == reverseSeq(inputSeq)[|inputSeq| - i - 1] //elementele sunt aceleasi dar inversate
// ensures forall i :: 0 <= i < |inputSeq| ==> reverseSeq(inputSeq)[i] == inputSeq[|inputSeq| - i - 1]
//  //seq de 0 si 1 si pe pozitia i este seq[|lngth|-i -1 ] aceleasi
// //reverse intoarce o secventa de job-uri care nu se suprapun, doar in unele cazuri  
// //1011 -> 1101
// {
//   if |inputSeq| == 0 then
//     inputSeq
//   else
//     reverseSeq(inputSeq[1..]) + [inputSeq[0]]
// }

predicate ValidPartialSolutions(allSol:seq<seq<int>>, jobs: seq<Job>,  index: int)
requires validJobsSeq(jobs)
{   
    |allSol| == index && forall i : int :: 0 <= i < index ==> isPartialSolution(allSol[i], jobs, i + 1) //pana la i + 1 inseamna pana la 2 -> 0 1 

}


ghost predicate isOptimalPartialSolution(solution: seq<int>, jobs: seq<Job>, length : int)
requires validJobsSeq(jobs) 
requires 0 <= length <= |jobs|
{ 
    isPartialSolution(solution, jobs, length) && 
    forall otherSol :: isPartialSolution(otherSol, jobs, length) ==>  PartialSolutionProfit(solution, jobs, 0, length) >=  PartialSolutionProfit(otherSol, jobs, 0, length)
}

predicate isOptimalPartialSolutionDP(solution: seq<int>, jobs: seq<Job>, length : int, dp:int)
requires validJobsSeq(jobs) 
//requires |solution| == length
requires 0 <= length <= |jobs|
//profit == dp
{ 
    isPartialSolution(solution, jobs, length) && PartialSolutionProfit(solution, jobs, 0, length) ==  dp
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

//am nevoie de un predicat isOptimalPartialSolution + i 

ghost predicate isOptimalSolution(solution: seq<int>, jobs: seq<Job>)
requires validJobsSeq(jobs) // este in regula ?
requires |solution| == |jobs| // sa primeasca i  + predicat isOptimalPartialSolution(index = |jobs|)
//profit == dp
{ 
    isSolution(solution, jobs) && 
    forall otherSol :: isSolution(otherSol, jobs) ==>  SolutionProfit(solution, jobs, 0) >=  SolutionProfit(otherSol, jobs, 0)
}

predicate isOptimalSolutionDP(solution: seq<int>, jobs: seq<Job>, dp: int)
requires validJobsSeq(jobs) 
requires |solution| == |jobs|
//profit == dp
{ 
    isSolution(solution, jobs) && SolutionProfit(solution, jobs, 0) == dp
}


// predicate JobBefore(job1:Job, job2: Job)
// requires validJob(job1)
// requires validJob(job2)
// {
//    job2.jobEnd <= job1.jobStart
// }


// predicate hasJust0(partialSol: seq<int>, jobs: seq<Job>)
// requires validJobsSeq(jobs)
// // requires 0 <= j < i < |jobs|
// // requires i - j + 1 == |partialSol|
// {
//     |partialSol| <= |jobs|  && forall x :: 0 <= x < |partialSol| - 1 ==> partialSol[x] == 0
// }


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
requires ValidPartialSolutions(allSol, jobs, i) //cerem ca all sol sa contina doar secvente de 0 si 1 si pentru toate 0 <= j < i allSol[j] == j + 1
ensures isPartialSolution(partialSolution, jobs, i + 1)
//ensures maxProfit == PartialSolutionProfit(partialSolution, jobs, 0, i + 1)
ensures  maxProfit == PartialSolutionProfit2(partialSolution, jobs, 0, 0, i + 1)
{       
       //max profit intoarce si solutia
        var max_profit := jobs[i].profit;
        var subSol := [1];
        var j := i - 1;
        var length := 1;
        //var left :int := 0;
        //var right :int := 0;
        //var left := 0;
        while j >= 0
            invariant -1 <= j <= i - 1
            decreases j
            //invariant 1 <= |subSol| <= i + 1 // ar trebui sa arat ca pentru i se obtine o solutie de lungime i + 1
            decreases  i - |subSol| 
            invariant 1 <= length <= i + 1 // trebuie sa demonstrez ca |allSol[j]| nu depaseste 
            //invariant length == i - j + 1 // pt i = 1, length = 2 
            decreases i - length
            invariant length == i - j 
            //invariant 1 <= |allSol| <= i
            //invariant |allSol| == i
            //invariant  isPartialSolution(subSol, jobs, length)
            invariant i - j == |subSol|
            invariant hasNoOverlappingJobs2(subSol, jobs, i, j + 1)
            invariant areOrderedByEnd2(subSol, jobs, i, j + 1)
            invariant j < |allSol|
            invariant j >= 0 ==> |allSol[j]| == j + 1
            invariant j >= 0 ==> isPartialSolution(allSol[j], jobs, j + 1)
            invariant |subSol| == length
            invariant forall i :: 0 <= i <= length - 1 ==> 0 <= subSol[i] <= 1
            invariant j != -1 ==> forall k :: 0 <= k < |subSol| - 1 ==> subSol[k] == 0
            invariant max_profit == PartialSolutionProfit2(subSol, jobs, 0, j + 1, length) 

        {   
            //job-ul j poate sa se termine la ora la care job-ul i incepe 
            if (jobs[j].jobEnd <= jobs[i].jobStart && j < |dp| && j < |allSol|) {
                assert max_profit == PartialSolutionProfit2(subSol, jobs, 0, j + 1, length);
                //am gasit o solutie partiala optima care nu se suprapune cu solutia noastra partiala 
                //este suficient sa gasim un job.actEnd < job.current fiind ordonate in functie de timpul de sfarsit 
                //allSol[j] poate sa contina job-ul j sau nu (deoarece se poate obtine sau nu o solutie partiala optima cu el)
                //dar pe noi ne intereseaza sa nu se suprapuna, mai exact sa se termine inainte ca job-ul nostru i sa inceapa 
                //left := j;
                max_profit := max_profit + dp[j];
                assert |subSol| == length;
                ghost var length' := length;
                assert  hasNoOverlappingJobs2(subSol, jobs, i, j+1); //verificam de la pozitia j+1 pana la i, asa se formeaza subSol 
                //assert isPartialSolution(subSol, jobs, length');
                assert !overlappingJobs(jobs[j], jobs[i]);
                assert forall k :: 0 <= k < |allSol[j]| ==> !overlappingJobs(jobs[k], jobs[i]); //niciun job din seq1 nu se suprapune cu job-ul i 
                assert hasNoOverlappingJobs(allSol[j], jobs); //allSol[j] contine job-uri care nu se suprapun 
                assert forall k, m :: 0 <= k < m < |allSol[j]| ==> (allSol[j][k] == 1 && allSol[j][m] == 1 ) ==>!overlappingJobs(jobs[k], jobs[m]);
                length := length + |allSol[j]|; //|allSol[j]| are lungimea j + 1, se stie din ipoteza (length + j + 1 nu este > i + 1)
                assert jobs[j].jobEnd <= jobs[i].jobStart;
                //assert notOverlappingJobs(jobs, j, j + 1); 
                //pana la ultima pozitie din subSol avem doar valori de 0 
                //assert subSol[0] == 0;
                //assert forall m :: 0 <= m < |subSol| - 1  ==> subSol[m] == 0;
                //assert forall k :: 0 <= k < |subSol| ==> subSol[k] == 1 ==> !overlappingJobs(jobs[j], jobs[j+k-1]); //trebuie sa demonstrez si pentru restul job-urilor din subSol (= 0)
                //assert !overlappingJobs(jobs[j], jobs[j+1]);
                Add2NotOverlappingSeq(allSol[j], subSol, jobs, i, j);
                subSol := allSol[j] + subSol;//trebuie sa ne asiguram ca allSol este format din solutii partiale (did it))
                //allSol[j] este solutia partiala optima cu job-urile pana la pozitia j inclusiv 
                assert hasNoOverlappingJobs(subSol, jobs);
                assert |subSol| == length;
                assert forall i :: 0 <= i <= length' - 1  ==> 0 <= subSol[i] <= 1;
                assert isPartialSolution(allSol[j], jobs, j + 1);
                assert forall i :: 0 <= i <= length - 1 ==> 0 <= subSol[i] <= 1;
                assert ValidPartialSolutions(allSol, jobs, i);
                //assert forall i :: 1 <= i < |subSol| ==> subSol[i] == 1 ==> jobs[j].jobEnd <= jobs[subSol[i]; 
                //assert jobs[j].jobEnd <= subSol[0];
                assert hasNoOverlappingJobs(subSol, jobs); //verificam de la pozitia 0 pana la pozitia |subSol| - 1
                j := 0;
                //assume isPartialSolution(subSol, jobs, |subSol|);
            }
            else
            {   
                assert max_profit == PartialSolutionProfit2(subSol, jobs, 0, j + 1, length);
                assert forall m :: 0 <= m < |subSol| - 1  ==> subSol[m] == 0;
                length := length + 1;
                subSol := [0] + subSol; //as adauga i zerouri de ex pt i = 1 adaug 1, pt i = 2 adaug 2 (pozitiile 1, 0 verific)  
                assert forall i :: 0 <= i <= length - 1 ==> 0 <= subSol[i] <= 1;
                assert hasNoOverlappingJobs2(subSol, jobs, i, j);
                assert subSol[0] == 0;
                //assert isPartialSolution(subSol, jobs, length);
                //solutia partiala se formeaza de la sfarsit spre inceputul listei cu job-uri
                //deci nu pot demonstra !overlappSeq deoarece pe prima pozitie va fi job-ul de index i, apoi i-1.. , unde i va avea pe rand valorile 1,2,3 s.a.m.d
                //iar in predicatul isPartialSolution am nevoie de o solutiePartiala ordonata/reprezentativa secventei de job-uri 
                // adica index 0 este pentru jobs[0] s.a.m.d
                max_profit := max_profit + 0 ;
                assert max_profit == PartialSolutionProfit2(subSol, jobs, 0, j, length);
            }
            j := j - 1;

            
        } 

        maxProfit := max_profit;
        //subSol este solutia partiala ce contine job-ul i 
        partialSolution := subSol;
        assert |partialSolution| == length;
        assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolution[i] <= 1;
        assert hasNoOverlappingJobs(partialSolution, jobs);
        assert isPartialSolution(partialSolution, jobs, length);
        assert max_profit == PartialSolutionProfit2(subSol, jobs, 0, j + 1, length);
        //assert maxProfit == PartialSolutionProfit(partialSolution, jobs, 0, i + 1);

        // print("Sulutiile ", solution);
        ///abia la sf pot demonstra ca solution este solutie partiala deoarece solutia este ordonata conform cu secventa de job-uri

        
}
method WeightedJobScheduling(jobs: seq<Job>) returns (sol: seq<int>, profit : int)
    requires |jobs| >= 1
    requires validJobsSeq(jobs)
    requires distinctJobsSeq(jobs)
    requires sortedByActEnd(jobs)
    ensures isSolution(sol, jobs)
    //ensures isOptimalSolution(sol, jobs)
    //ensures isOptimalSolution(sol)
    //ensures ProfitRecursiveHelper(sol, jobs, 0 ) == profit

{   
    var dp :seq<int> := [];
    var dp0 := jobs[0].profit; //dynamic programming
    dp := dp + [dp0]; 
    // print(dp[0]);
    var solution : seq<int> := [1];
    print("Sol: ", solution);
    print("DP: ", dp);
    var i: int := 1;
    var allSol : seq<seq<int>> := [];
    allSol := allSol + [[1]]; //adaugam solutia pana la primul job inclusiv 
    //var maxProfit := 0;
    while i < |jobs| 
        invariant 1 <= i <= |jobs|
        decreases |jobs| - i
        invariant i == |dp|
        invariant 1 <= |dp| <= |jobs|
        decreases |jobs| - |dp|
       // invariant 1 <= |solution| <= i + 1
        invariant isPartialSolution(solution, jobs, i)
        invariant i == |allSol|
        decreases |jobs| - |allSol|
        invariant |allSol[i-1]| == i 
        invariant 1 <= |allSol[i-1]| <= |jobs|
        decreases |jobs| - |allSol[i-1]| 
        invariant isPartialSolution(allSol[i-1], jobs, i)
        invariant ValidPartialSolutions(allSol, jobs, i) //i = 1, allSol are lungime 1 , deci doar AllSol[0] exista 
        invariant dp[i-1] == PartialSolutionProfit(solution, jobs, 0, i)
        invariant dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i)
        invariant OptimalPartialSolutions(allSol, jobs, dp, i)
        invariant isOptimalPartialSolutionDP(solution, jobs, i, dp[i-1])
        //solutie partiala optima solutia pentru i 
        //1)invariant dp[i] == profit(allSol[i])
        //2)predicat isOptimal 
        //nu stie cate elemente are allSol 
    {   //invariant [0,1...](sol) solutie partial //solutie partiala optima 
        //castigul pt sol partiala este dp
        // sa aratam ca nicio alta solutie partiala de aceeasi lungime nu are castig mai bun 
        //print("Sol: ", solution);
        var maxProfit, solForCurrentJobIncluded := MaxProfit(jobs, i, dp, allSol); 
        //calculeaza maximul dintre excluded profit si included profit 
        //maximul dintre profitul obtinut pana la job-ul anterior si profitul obtinut cu adugarea job-ului curent  
        if dp[i-1] >= maxProfit
        {   
            //assert dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i);
            dp := dp + [dp[i-1]]; //profitul general ramane profitul anterior deoarece prin prin selectarea job-ului curent nu se obtine un profit mai mare  
            solution := solution + [0];
            assert dp[i] == PartialSolutionProfit(solution, jobs, 0, i + 1);
            //abia aici fac compararea si aici ar trebui sa modific/creez solution 
            //aici ar trebui sa ramanem la solution anterior, deoarece s-a obtinut un profit mai bun fara job-ul curent 
            assert isPartialSolution(solution, jobs, i + 1);
        }
        else 
        {   
            //assert dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i);
            dp := dp + [maxProfit]; //profitul general creste deorece cu job-ul curent se obtine un profit mai mare 
            solution := solForCurrentJobIncluded; 
            assert dp[i] == PartialSolutionProfit(solution, jobs, 0, i + 1);
            assert isPartialSolution(solution, jobs, i + 1);
            //aici solution ar trebui sa ia valoarea generata de MaxProfit pentru ca job-ul curent se adauga deci solutia va fi aceea care il contine 
        }
        print("Sol: ", solution);
        print("DP: ", dp);
        assert dp[i-1] == PartialSolutionProfit(allSol[i-1], jobs, 0, i);
        allSol := allSol + [solution]; //cream secventa de solutii(care includ job-ul curent sau nu) pentru fiecare job in parte 
        //allSol[j] = contine solutia partiala optima pana la pozitia j inclusiv (formata din job-urile pana la pozitia j inclusiv, partiala optima)
        print("Allsol: ", allSol);
        //assert isPartialSolution(allSol[i-1], jobs, i);
        //assert ValidPartialSolutions(allSol, jobs, i+1);
        i := i + 1;
    }
    
    //sol := Solution(jobs, dp);
    sol := solution;
    profit := dp[|dp|-1];
}


method Main()
{   
    // var job1: Job := Pair(jobStart := 1, jobEnd := 2, profit := 50);
    // var job2: Job := Pair(jobStart := 3, jobEnd := 5, profit := 20);
    // var job3: Job := Pair(jobStart := 6, jobEnd := 19, profit := 100);
    // var job4: Job := Pair(jobStart := 2, jobEnd := 100, profit := 200);
    // var jobs: seq<Job> := [job1, job2, job3, job4];
    var job1: Job := Pair(jobStart := 0, jobEnd := 10, profit := 1);
    var job2: Job := Pair(jobStart := 15, jobEnd := 25, profit := 1);
    var job3: Job := Pair(jobStart := 30, jobEnd := 40, profit := 1);
    var job4: Job := Pair(jobStart := 20, jobEnd := 50, profit := 1);
    var job5: Job := Pair(jobStart := 60, jobEnd := 70, profit := 1);
    var jobs: seq<Job> := [job1, job2, job3, job4, job5];
    // print(jobs[..1]);
    // print(|jobs[..1]|);
    var s : seq<seq<int>> := [[1, 2, 2]];
    s := s + [[2]];
    // print(s);
    print(|s|);
    var secventa : seq<int> := [1,1,1];
    // print(s[0]);
    //secventa de job-uri trebuie sa fie valida (1)
    //-----------------------------------contina job-uri diferite din pctdv al cel putin un timp (st sau sf)  
    var solutie : seq<int> := [];
    var profit : int := 0;
    solutie, profit := WeightedJobScheduling(jobs);
    print ("Solutia: ", solutie);
    //solutia trebuie sa contina job-uri care nu se suprapun si sa fie de profit maxim 
    
}
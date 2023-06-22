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
    j1.jobEnd >= j2.jobStart && j1.jobStart <= j2.jobEnd
}

predicate disjointJobsSeq(jobs: seq<Job>)
requires validJobsSeq(jobs)
{
    distinctJobsSeq(jobs) &&
    forall i1, i2 :: 0 <= i1 < i2 < |jobs| ==> !overlappingJobs(jobs[i1], jobs[i2])
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


predicate isSolution(solution: seq<int>, jobs: seq <Job>) //sa primeasca si datele de intrare (problema) , solutie pt porblema, not overlap

{ 
    //daca solution[i] == 1 apelez !overlapping ==> if
    isPartialSolution(solution, jobs, |jobs|)
}


predicate isPartialSolution(partialSol : seq <int>, jobs: seq<Job>, index: int) //problema, doar o solutie, not overlap, + index 
{   
    |partialSol| == index && forall i :: 0 <= i <= |partialSol| - 1  ==> 0 <= partialSol[i] <= 1 // + predicatul !overlapp 
    //&& forall i, j :: 0 <= i < j < |partialSol| ==> if (partialSol[i] == 1 && partialSol[j] == 1) then !overlappingJobs(jobs[i], jobs[j]) else false
}



function reverseSeq(inputSeq: seq<int>) : seq<int>
ensures |inputSeq| == |reverseSeq(inputSeq)| //are aceeasi lungime 
ensures forall i :: 0 <= i < |inputSeq| ==> inputSeq[i] == reverseSeq(inputSeq)[|inputSeq| - i - 1] //elementele sunt aceleasi dar inversate
ensures forall i :: 0 <= i < |inputSeq| ==> reverseSeq(inputSeq)[i] == inputSeq[|inputSeq| - i - 1]
 //seq de 0 si 1 si pe pozitia i este seq[|lngth|-i] aceleasi 
{
  if |inputSeq| == 0 then
    inputSeq
  else
    reverseSeq(inputSeq[1..]) + [inputSeq[0]]
}


predicate ValidPartialSolutions(allSol:seq<seq<int>>, jobs: seq<Job>,  index: int)
//requires 1 <= |allSol| <= index //lungime 1 -> avem doar pe pozitia 0 element 
{   //daca i este 1 trebuie sa vedem ca allSol[0] sa fie solutie partiala 
    |allSol| == index && forall i : int :: 0 <= i < index ==> isPartialSolution(allSol[i], jobs, i + 1) //pana la i + 1 inseamna pana la 2 -> 0 1 
    //daca index este 1 inseamna ca i o sa aiba doar valorea 0 
    //nu are de unde sti ca allSol este format din secvente de 0 si 1 
}

method MaxProfit(jobs: seq <Job>, i: int, dp: seq<int>, allSol :seq<seq<int>>) returns (maxProfit:int, solution: seq<int>)
requires |jobs| >= 2
requires validJobsSeq(jobs)
requires distinctJobsSeq(jobs)
requires sortedByActEnd(jobs)
requires 1 <= i < |jobs|
requires 1 <= |dp| < |jobs|
requires 1 <= |allSol| <= |jobs|
requires |allSol| == i 
requires ValidPartialSolutions(allSol, jobs, i) //cerem ca all sol sa contina doar secvente de 0 si 1 si pentru toate 0 <= j < i allSol[j] == j + 1
ensures isPartialSolution(solution, jobs, i + 1)
//requires(allSol)

{       
       //max profit intoarce si solutia
        var max_profit := jobs[i].profit;
        var subSol := [1];
        var j := i - 1;
        var length := 1;
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
            invariant  isPartialSolution(subSol, jobs, length)
            //invariant isPartialSolution(allSol[j], jobs, j + 1) //nu stie cate elemente are allSol ??
            invariant j < |allSol|
            //invariant 0 <= j <= i - 1 ==> 1 <= |allSol[j]| <= i
            invariant j >= 0 ==> |allSol[j]| == j + 1
            //subSol reprezinta o solutie partiala ce contine job-ul i 
            //invariant isPartialSolution(subSol, jobs, i-j) //i = 1 --> ..1 => doar de pe pozitia 0 ==> 1 elem i = 1 => j = 0 
            //ce prop are subsol 
            //invariant j == i - 1 ==> |allSol[j]| == i  
            //invariant j >= 0  ==> |allSol[j]| == i - j - 1 //allsol[0] == 1, allsol[1] == 2, allSol[2] == 3, (allSol[3] == 4) 
            invariant j >= 0 ==> isPartialSolution(allSol[j], jobs, j + 1)

        {
            if (jobs[j].jobEnd <= jobs[i].jobStart && j < |dp| && j < |allSol|) {
                max_profit := max_profit + dp[j];
                assert |subSol| == length;
                ghost var length' := length;
                length := length + |allSol[j]|; //|allSol[j]| are lungimea j + 1, se stie din ipoteza (length + j + 1 nu este > i + 1)
                subSol := subSol + reverseSeq(allSol[j]);
                assert |subSol| == length;
                //assert forall i :: 0 <= i < |allSol[j]| ==> allSol[j][i] == reverseSeq(allSol[j])[|allSol[j]| - i - 1];
                assert forall k :: 0 <= k < |allSol[j]| ==> reverseSeq(allSol[j])[k] == allSol[j][|allSol[j]| - k - 1];
                assert forall i :: 0 <= i <= length' - 1  ==> 0 <= subSol[i] <= 1;
                assert isPartialSolution(allSol[j], jobs, j + 1);
                assert forall i :: 0 <= i <= length - 1 ==> 0 <= subSol[i] <= 1;
                assert isPartialSolution(subSol, jobs, length);
            
                break;
            }
            else
            {   
                length := length + 1;
                subSol := subSol + [0]; //as adauga i zerouri de ex pt i = 1 adaug 1, pt i = 2 adaug 2 (pozitiile 1, 0 verific)  
                assert isPartialSolution(subSol, jobs, length);
            }
            j := j - 1;

            
        } 
        
        maxProfit := max_profit;
        solution := reverseSeq(subSol);
        // print("Sulutiile ", solution);
        
}
method WeightedJobScheduling(jobs: seq<Job>) returns (sol: seq<int>)
    requires |jobs| >= 2
    requires validJobsSeq(jobs)
    requires distinctJobsSeq(jobs)
    requires sortedByActEnd(jobs)
    //ensures isSolution(sol)
    //ensures isOptimalSolution(sol)
    //ensures ValidPartialSolutions(allSol, jobs, )

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
            dp := dp + [dp[i-1]]; //profitul general ramane profitul anterior deoarece prin prin selectarea job-ului curent nu se obtine un profit mai mare  
            solution := solution + [0];
            //abia aici fac compararea si aici ar trebui sa modific/creez solution 
            //aici ar trebui sa ramanem la solution anterior, deoarece s-a obtinut un profit mai bun fara job-ul curent 
            assert isPartialSolution(solution, jobs, i + 1);
        }
        else 
        {
            dp := dp + [maxProfit]; //profitul general creste deorece cu job-ul curent se obtine un profit mai mare 
            solution := solForCurrentJobIncluded; 
            assert isPartialSolution(solution, jobs, i + 1);
            //aici solution ar trebui sa ia valoarea generata de MaxProfit pentru ca job-ul curent se adauga deci solutia va fi aceea care il contine 
        }
        print("Sol: ", solution);
        print("DP: ", dp);
        allSol := allSol + [solution]; //cream secventa de solutii(care includ job-ul curent) pentru fiecare job in parte 
        //assert isPartialSolution(allSol[i-1], jobs, i);
        //assert ValidPartialSolutions(allSol, jobs, i+1);
        i := i + 1;
    }
    
    //sol := Solution(jobs, dp);
    sol := solution;
}


method Main()
{   
    var job1: Job := Pair(jobStart := 1, jobEnd := 2, profit := 50);
    var job2: Job := Pair(jobStart := 3, jobEnd := 5, profit := 20);
    var job3: Job := Pair(jobStart := 6, jobEnd := 19, profit := 100);
    var job4: Job := Pair(jobStart := 2, jobEnd := 100, profit := 200);
    var jobs: seq<Job> := [job1, job2, job3, job4];
    // print(jobs[..1]);
    // print(|jobs[..1]|);
    var s : seq<seq<int>> := [[1, 2, 2]];
    s := s + [[2]];
    // print(s);
    print(|s|);
    // print(s[0]);
    var solutie: seq<int> := WeightedJobScheduling(jobs);
    print ("Solutia: ", solutie);
    
}
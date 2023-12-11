// Unfinished and has many mistakes, apologies, i'm commiting to main because I have 1 day before exam and want this on my laptop
// when I wake up. ;)

// All but one integers in s1 appear in s2
//predicate q_2022bi(s1: seq<int>, s2: seq<int>)
//{
//    exists i :: (0 <= i < |s1| &&
//        forall l :: (0 <= l < |s2| ==> s1[i] != s2[l]) &&
//        forall j :: (0 <= j < |s1| && s1[i] != s2[j] ==>
//            exists k :: (0 <= k < |s2| && s1[i] == s2[k])
//        )
//    )
//}

predicate q_2022bii(s1: seq<int>, s2: seq<int>, s3: seq<int>)
{
    forall i :: (0 <= i < |s1| ==>
        forall j :: (0 <= j < |s2| && s1[i] == s2[j] ==>
            !(exists k :: (0 <= k < |s3| && s1[i] == s3[k]))
        )
    )
}

predicate q_2022biii(s1: seq<int>, s2: seq<int>, s3: seq<int>)
{
    forall i :: (0 <= i < |s1| ==> 
        !(exists l :: (0 <= l < |s1| && s1[i] == s1[l] && i != l)) && 
        forall j :: (0 <= j < |s2| && s1[i] != s2[j] ==>
                forall k :: (0 <= k < |s3| ==> s1[i] == s3[k])
        )
    )
}

//predicate qtest_2022biii(s1: seq<int>, s2: seq<int>, s3: seq<int>)
//{
//    forall i :: (0 <= i < |s1| ==> 
//        !(exists j :: (0 <= j < |s1| && s1[i] == s1[j] && i != j)) &&
//        !(exists k :: (0 <= k < |s2| && s2[k] == s1[i] &&
//            exists l :: (0 <= l < |s3| && s1[i] == s3[l]))
//         )
//    )
//}
predicate b2022biii2(s1: seq<int>, s2: seq<int>, s3: seq<int>)
{
    forall i,j:: 0<= i < j < |s1| && s1[i]!=s1[j] ==>
        forall k :: 0 <= k < |s2| && s1[i]!=s2[k] ==>
            exists l :: 0 <= l < |s3| && s1[i]==s3[l] 
}

predicate q_2021bi(s1:seq<int>, s2: seq<int>)
{
    exists i :: 0 <= i < |s1| &&
        !(exists j, k :: 0 <= j < k < |s2| && s1[i] == s2[j] && s1[i] == s2[k]) &&
        (exists l :: 0 <= l < |s2| && s1[i] == s2[l])
}

predicate q_2021bii(s1:seq<int>, s2: seq<int>, s3: seq<int>)
{
    forall i :: 0 <= i < |s1| ==>
        (exists j :: 0 <= j < |s2| && s1[i] == s2[j]) ||
        (exists k :: 0 <= k < |s3| && s1[i] != s3[k])
}

method Main()
{
    var s1 := [1,1,1,2,3,4,5];
    var s2 := [1,2,3,7,8];
    var s3 := [4];
    var res := b2022biii2(s1, s2, s3);
    print res, "\n";

    s1 := [1,2,3,7];
    s2 := [1];
    res := q_2021bi(s1, s2);
    print res, "\n";

    s1 := [1,2,3,7];
    s2 := [1,2,3,7];
    s3 := [1,2];
    res := q_2021bii(s1, s2, s3);
    print res, "\n";
}

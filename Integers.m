(* ::Package:: *)

(* ::Input:: *)
(*BeginPackage["Integers`"]*)


npf::usage="npf[n,p,t]"


Solution::usage=""


Bootstrap::usage="Bootstrap[\[CapitalDelta],size,sgap]"


e::usage="e[l,n,\[CapitalDelta]]"


Subscript[e, m]::usage="\!\(\*SubscriptBox[\(e\), \(m\)]\)[n,\[CapitalDelta]]"


new::usage="new"


fullset::usage="fullset"


Begin["Private`"]


new="npf[n,a,t] evaluate the function \!\(\*FractionBox[\(\*SuperscriptBox[SubscriptBox[\(f\), \(p\)], \(n\)] \((t)\)\), \(n!\)]\)

e[l,n,\[CapitalDelta]] give us the OPE coefficients for the most general 4-point function with \!\(\*SubscriptBox[\(\[CapitalDelta]\), \(\[Phi]\)]\)=\[CapitalDelta] in the basis \[CapitalBeta]={(a,b,c)/a,b,c,\[CapitalDelta] \[Element] \!\(\*SubscriptBox[\(\[CapitalZeta]\), \(\(\[GreaterEqual]\)\(0\)\)]\) && a+b+c=2\[CapitalDelta]} \n \n \!\(\*SubscriptBox[\(e\), \(m\)]\)[n,\[CapitalDelta]] give us the limit \!\(\*FractionBox[\(e[l, n, \[CapitalDelta]]\), FractionBox[\(\*SqrtBox[\(2  \[Pi]\)] \*SuperscriptBox[\((n + l)\), \(2  \[CapitalDelta] - \*FractionBox[\(3\), \(2\)]\)]\), \(\*SuperscriptBox[\(2\), \(2  n + 2  l - \*FractionBox[\(3\), \(2\)]\)] \*SuperscriptBox[\(Gamma[\[CapitalDelta]]\), \(2\)]\)]]\), l \[Rule] \[Infinity]

the fullset give us all of the independent coefficients in our 4-point function and Solution give us a rule with the values found by the Bootstrap function 

Bootstrap[\[CapitalDelta],size,sgap] searches for a 4-point function with scalar gap \[GreaterEqual] 2sgap and positive OPE coefficients for the operators with \!\(\*FractionBox[\(\[Tau]\), \(2\)]\) = n \[LessEqual] size and J \[LessEqual] size

it then tests to see if the solution found is unitary."


(* ::Chapter::Closed:: *)
(*Definitions*)


norm[t_]:=If[t==0,1/2,1];
npf[n_,p_,t_]:=If[n>1,Gamma[n+p]^2/(n!Pochhammer[2p-1+n,n]) HypergeometricPFQRegularized[{-n,2p+n-1,p/2-t},{p,p},1],If[n>=0,1+n(t-1),0]];
e[l_,n_,\[CapitalDelta]_]:=Sum[2 norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[n+l-i,i,\[CapitalDelta]-j-i/2]npf[n-i,i,\[CapitalDelta]-j-i/2],{i,0,2\[CapitalDelta]},{j,0,\[CapitalDelta]-i/2}];
Subscript[e, m][n_,\[CapitalDelta]_]:=Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,2\[CapitalDelta]}];


(* ::Chapter::Closed:: *)
(*Bootstrap function*)


Bootstrap[\[CapitalDelta]_,size_,sgap_]:= Do[


(* part 1 *)




fullset = DeleteDuplicates[Table[a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]],{i,0,2\[CapitalDelta]},{j,0,\[CapitalDelta]-i/2}]//Flatten];

Equation = Apply[And,Table[e[0,i,\[CapitalDelta]]==KroneckerDelta[i,0],{i,0,sgap-1}]];

Solution1 = Solve[Equation]//Flatten;

If[Length[Solution1]==0,Print["The gap cannot be reached"]; Break[];,Print["Solution1 was found"];];

PartialSet = {};

For[i=0,i<=2\[CapitalDelta],i++,For[j=0,j<=\[CapitalDelta]-i/2,j++,If[D[(a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]/.Solution1),a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]]==1,AppendTo[PartialSet,a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]]]]];

PartialSet=DeleteDuplicates[PartialSet];

condition = Apply[And,({0<a[0,0]<1/.Solution1})~Join~Table[e[l,n,\[CapitalDelta]]>=0/.Solution1,{n,0,size},{l,0,size,2}]~Join~Table[Subscript[e, m][n,\[CapitalDelta]]>0/.Solution1,{n,0,size}]//Flatten];

Solution2=FindInstance[condition,PartialSet]//Flatten;

If[Length[Solution2]==0,Print["There is no unitary solution"];Break[];,Print["Solution2 was found"];];

Solution=Union[Solution1/.Solution2,Solution2];



(* part2 *)



stopN=Max[2Ceiling[(Sqrt[2] \[CapitalDelta]^(3/2)+\[CapitalDelta]/4-95/(32Sqrt[2]) \[CapitalDelta]^(1/2)-9/8)/2],2Ceiling[size/2]];

stopL=Max[2Ceiling[(Sqrt[2] \[CapitalDelta]^(3/2)+\[CapitalDelta]/4-95/(32Sqrt[2]) \[CapitalDelta]^(1/2)-9/8)/2],2Ceiling[size/2]];

Positivity=0;

Test1=Apply[And,Table[Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,k}]>=0/.Solution,{k,0,2\[CapitalDelta]-2}]];

Test2=Apply[And,Table[norm[2\[CapitalDelta]-2-k]a[Min[k,1],Min[Max[1,k],2\[CapitalDelta]-1-k]]+Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,k}]>=0/.Solution,{k,0,2\[CapitalDelta]-2}]];

If[Test1&&Test2,

list=Table[a[Min[2\[CapitalDelta]-2j-i,j],Min[Max[i,j],2\[CapitalDelta]-(-i+j)]](*npf[stopN-i,i,\[CapitalDelta]-j-i/2]*),{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]/.Solution;

brake=False;

For[i=1,i<=Length[list],i++,For[j=1,j<=Length[list[[i]]],j++,If[brake,Break[];]; If[(list[[i,j]]<0)||(i==Length[list]&&j==Length[list[[i]]]),brake=True; value={i+1,2\[CapitalDelta]-2(i+1)-(j-1)};Break[];];];];


Monitor[While[(({{(1+a[0,0])npf[stopN-2\[CapitalDelta]+1,2\[CapitalDelta]-1,1/2]^2/.Solution},Table[2Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,k}]npf[stopN-2\[CapitalDelta]+1,2\[CapitalDelta]-1,1/2]npf[stopN-k,k,\[CapitalDelta]-1-k/2]/.Solution,{k,2\[CapitalDelta]-2,0,-1}],Table[((KroneckerDelta[k,j]a[Min[k,1],Min[Max[1,k],2\[CapitalDelta]-1-k]]norm[2\[CapitalDelta]-2-k]+Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,Min[k,j]}])npf[stopN-j,j,\[CapitalDelta]-1-j/2]npf[stopN-k,k,\[CapitalDelta]-1-k/2])/.Solution,{k,2\[CapitalDelta]-2,0,-1},{j,2\[CapitalDelta]-2,0,-1}]}~Join~Table[If[value[[1]]<=j,If[(value[[2]]>=i)||(value[[1]]<j),If[a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]>=0/.Solution,0,1],1],1]norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[stopN-i,i,\[CapitalDelta]-j-i/2]^2/.Solution,{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]//Flatten//Total)<0)||(({{(1-a[0,0])npf[stopN-2\[CapitalDelta]+2,2\[CapitalDelta]-1,1/2]^2/.Solution},Table[2Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,k}]npf[stopN-2\[CapitalDelta]+2,2\[CapitalDelta]-1,1/2]npf[stopN-k+1,k,\[CapitalDelta]-1-k/2]/.Solution,{k,2\[CapitalDelta]-2,0,-1}],Table[((KroneckerDelta[k,j]a[Min[k,1],Min[Max[1,k],2\[CapitalDelta]-1-k]]norm[2\[CapitalDelta]-2-k]+Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,Min[k,j]}])npf[stopN-j+1,j,\[CapitalDelta]-1-j/2]npf[stopN-k+1,k,\[CapitalDelta]-1-k/2])/.Solution,{k,2\[CapitalDelta]-2,0,-1},{j,2\[CapitalDelta]-2,0,-1}]}~Join~Table[If[value[[1]]<=j,If[(value[[2]]>=i)||(value[[1]]<j),If[a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]>=0/.Solution,0,1],1],1]norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[stopN-i+1,i,\[CapitalDelta]-j-i/2]^2/.Solution,{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]//Flatten//Total)<0),Positivity+=(e[0,stopN,\[CapitalDelta]]>=0/.Solution/.{True->0,False->1})+(e[0,stopN+1,\[CapitalDelta]]>=0/.Solution/.{True->0,False->1}); stopN+=2;];,stopN];


,

Monitor[While[(({{(1+a[0,0])npf[stopN-2\[CapitalDelta]+1,2\[CapitalDelta]-1,1/2]^2/.Solution},Table[If[Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,k}]>=0/.Solution,0,1]2Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,k}]npf[stopN-2\[CapitalDelta]+1,2\[CapitalDelta]-1,1/2]npf[stopN-k,k,\[CapitalDelta]-1-k/2]/.Solution,{k,2\[CapitalDelta]-2,0,-1}],Table[If[(KroneckerDelta[k,j]a[Min[k,1],Min[Max[1,k],2\[CapitalDelta]-1-k]]norm[2\[CapitalDelta]-2-k]+Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,Min[k,j]}])>=0/.Solution,0,1]((KroneckerDelta[k,j]a[Min[k,1],Min[Max[1,k],2\[CapitalDelta]-1-k]]norm[2\[CapitalDelta]-2-k]+Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,Min[k,j]}])npf[stopN-j,j,\[CapitalDelta]-1-j/2]npf[stopN-k,k,\[CapitalDelta]-1-k/2])/.Solution,{k,2\[CapitalDelta]-2,0,-1},{j,2\[CapitalDelta]-2,0,-1}]}~Join~Table[If[a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]>=0/.Solution,0,1]norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[stopN-i,i,\[CapitalDelta]-j-i/2]^2/.Solution,{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]//Flatten//Total)<0)||(({{(1-a[0,0])npf[stopN-2\[CapitalDelta]+2,2\[CapitalDelta]-1,1/2]^2/.Solution},Table[If[Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,k}]>=0/.Solution,0,1]2Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,k}]npf[stopN-2\[CapitalDelta]+2,2\[CapitalDelta]-1,1/2]npf[stopN-k+1,k,\[CapitalDelta]-1-k/2]/.Solution,{k,2\[CapitalDelta]-2,0,-1}],Table[If[(KroneckerDelta[k,j]a[Min[k,1],Min[Max[1,k],2\[CapitalDelta]-1-k]]norm[2\[CapitalDelta]-2-k]+Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,Min[k,j]}])>=0/.Solution,0,1]((KroneckerDelta[k,j]a[Min[k,1],Min[Max[1,k],2\[CapitalDelta]-1-k]]norm[2\[CapitalDelta]-2-k]+Sum[a[0,Min[i,2\[CapitalDelta]-i]],{i,0,Min[k,j]}])npf[stopN-j+1,j,\[CapitalDelta]-1-j/2]npf[stopN-k+1,k,\[CapitalDelta]-1-k/2])/.Solution,{k,2\[CapitalDelta]-2,0,-1},{j,2\[CapitalDelta]-2,0,-1}]}~Join~Table[If[a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]>=0/.Solution,0,1]norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[stopN-i+1,i,\[CapitalDelta]-j-i/2]^2/.Solution,{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]//Flatten//Total)<0),Positivity+=(e[0,stopN,\[CapitalDelta]]>=0/.Solution/.{True->0,False->1})+(e[0,stopN+1,\[CapitalDelta]]>=0/.Solution/.{True->0,False->1}); stopN+=2;];,stopN];

];

stopLlist={};

For[n=0,n<stopN,n++,

If[n<=stopL,

stop=stopL;

list={{Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,2\[CapitalDelta]}]},Table[(Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,k}]+norm[\[CapitalDelta]-1-k/2]a[Min[1,k],Min[Max[1,k],2\[CapitalDelta]-1-k]]npf[n-k,k,\[CapitalDelta]-1-k/2]),{k,2\[CapitalDelta]-2,0,-1}]}~Join~Table[norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[n-i,i,\[CapitalDelta]-j-i/2],{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]/.Solution;

brake=False;

For[i=2,i<=Length[list],i++,For[j=1,j<=Length[list[[i]]],j++,If[brake,Break[];]; If[(list[[i,j]]<0)||(i==Length[list]&&j==Length[list[[i]]]),brake=True; value={i,j};Break[];];];];


Monitor[While[({{Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,2\[CapitalDelta]}]npf[stop+n-2\[CapitalDelta]+1,2\[CapitalDelta]-1,1/2]/.Solution},Table[If[value[[1]]<=2,If[value[[2]]<=2\[CapitalDelta]-1-k,If[(Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,k}]+norm[\[CapitalDelta]-1-k/2]a[Min[1,k],Min[Max[1,k],2\[CapitalDelta]-1-k]]npf[n-k,k,\[CapitalDelta]-1-k/2])>=0/.Solution,0,1],1],1](Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,k}]+norm[\[CapitalDelta]-1-k/2]a[Min[1,k],Min[Max[1,k],2\[CapitalDelta]-1-k]]npf[n-k,k,\[CapitalDelta]-1-k/2])npf[stop+n-k,k,\[CapitalDelta]-1-k/2]/.Solution,{k,2\[CapitalDelta]-2,0,-1}]}~Join~Table[If[value[[1]]<=j+1,If[(value[[2]]<=2\[CapitalDelta]-2j+1-i)||(value[[1]]<j+1),If[a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]>=0/.Solution,0,1],1],1]norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[n-i,i,\[CapitalDelta]-j-i/2]npf[stop+n-i,i,\[CapitalDelta]-j-i/2]/.Solution,{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]//Flatten//Total)<0,Positivity+=(e[stop,n,\[CapitalDelta]]>=0/.Solution/.{True->0,False->1}); stop+=2;];,{n,stop}];

AppendTo[stopLlist,stop];

,

stop=0;

list={{Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,2\[CapitalDelta]}]},Table[(Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,k}]+norm[\[CapitalDelta]-1-k/2]a[Min[1,k],Min[Max[1,k],2\[CapitalDelta]-1-k]]npf[n-k,k,\[CapitalDelta]-1-k/2]),{k,2\[CapitalDelta]-2,0,-1}]}~Join~Table[norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[n-i,i,\[CapitalDelta]-j-i/2],{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]/.Solution;

brake=False;

For[i=2,i<=Length[list],i++,For[j=1,j<=Length[list[[i]]],j++,If[brake,Break[];]; If[(list[[i,j]]<0)||(i==Length[list]&&j==Length[list[[i]]]),brake=True; value={i,j};Break[];];];];


Monitor[While[({{Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,2\[CapitalDelta]}]npf[stop+n-2\[CapitalDelta]+1,2\[CapitalDelta]-1,1/2]/.Solution},Table[If[value[[1]]<=2,If[value[[2]]<=2\[CapitalDelta]-1-k,If[(Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,k}]+norm[\[CapitalDelta]-1-k/2]a[Min[1,k],Min[Max[1,k],2\[CapitalDelta]-1-k]]npf[n-k,k,\[CapitalDelta]-1-k/2])>=0/.Solution,0,1],1],1](Sum[a[0,Min[i,2\[CapitalDelta]-i]]npf[n-i,i,\[CapitalDelta]-i/2],{i,0,k}]+norm[\[CapitalDelta]-1-k/2]a[Min[1,k],Min[Max[1,k],2\[CapitalDelta]-1-k]]npf[n-k,k,\[CapitalDelta]-1-k/2])npf[stop+n-k,k,\[CapitalDelta]-1-k/2]/.Solution,{k,2\[CapitalDelta]-2,0,-1}]}~Join~Table[If[value[[1]]<=j+1,If[(value[[2]]<=2\[CapitalDelta]-2j+1-k)||(value[[1]]<j+1),If[a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]>=0/.Solution,0,1],1],1]norm[\[CapitalDelta]-j-i/2]a[Min[i,j],Min[Max[i,j],2\[CapitalDelta]-(i+j)]]npf[n-i,i,\[CapitalDelta]-j-i/2]npf[stop+n-i,i,\[CapitalDelta]-j-i/2]/.Solution,{j,2,\[CapitalDelta]},{i,2\[CapitalDelta]-2j,0,-1}]//Flatten//Total)<0,Positivity+=(e[stop,n,\[CapitalDelta]]>=0/.Solution/.{True->0,False->1});stop+=2;];,{n,stop}];

AppendTo[stopLlist,stop];


]


];

If[Positivity==0,

Monitor[Positivity+=(Table[e[l,n,\[CapitalDelta]]>=0/.Solution/.{True->0,False->1},{n,0,Max[2Ceiling[(Sqrt[2] \[CapitalDelta]^(3/2)+\[CapitalDelta]/4-95/(32Sqrt[2]) \[CapitalDelta]^(1/2)-9/8)/2],2Ceiling[size/2]]},{l,2Ceiling[size/2]HeavisideTheta[size-n+1/2],Max[2Ceiling[(Sqrt[2] \[CapitalDelta]^(3/2)+\[CapitalDelta]/4-95/(32Sqrt[2]) \[CapitalDelta]^(1/2)-9/8)/2],2Ceiling[size/2]],2}]//Flatten//Total);,{n,l}];

, Print["The number of negative OPE coefficients is ",Positivity];Break[];];


Print["The number of negative OPE coefficients is ",Positivity];


,{1}]


(* ::Chapter:: *)
(*Test*)


End[];


(* ::Input:: *)
(*EndPackage[]*)

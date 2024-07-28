MODULE ProjGenLiMatin;

(* programme qui cherche des LCG selon le critere generalise *)
(* M_(d, T1, T2, T3, \ldots, T_d) *)
(* voir article pour Management Science *)


(* Myinout *)
FROM   MYINOUT  IMPORT  OpenAsInput, CloseInput, ReadLn, ReadLongInt, WriteString, WriteLn,
	                OpenAsOutput, CloseOutput, ReadBool, WriteBool, ReadInt, ReadLine,
	                ReadString, OpenOutput, OpenInput, ReadLongReal, WriteLongInt,
                        WriteLongReal;
FROM   MYSTR    IMPORT  Match;
FROM   NUM      IMPORT  Trunc, Sqrt, LIToLR, WriteLR, ModLR, WriteLI;

(* Latmrg *)
FROM   MULT     IMPORT  MReadScal, MScal, MDim, MVect, MCreateVect, LIToMScal,
                        MCreateScal, MWriteScal, SetFactors, MAffect, MScalToLR;
FROM   MRG      IMPORT  InitMRG, SpectralH, Verify0, CurOutTex, TestLa, Lacunary,
	                Test, Spectral, D2, S2, LatType, PerMax, MaxAllDim;
FROM   CONSTANT IMPORT  BDim;
FROM   BASIS    IMPORT  BVect, BCreateVect, BOne, BZero, BGreater, BScal, BAdd,
                        BAffect, BWriteScal, BWriteVect;
FROM   REDBAS   IMPORT  InitREDBAS, Critere2;
FROM   CONVERT  IMPORT  SupToMScal;
IMPORT BASISLR, MRG, REDBAS, LATBASIS;
FROM   LILR     IMPORT  BScalToMScal;


(* Sentiers *)
FROM   SUPFACT  IMPORT  Factors;
FROM   SUPCONV  IMPORT  SupToLongReal;
FROM   SUPINT   IMPORT  Create, Delete, WriteSup, SuperInteger, ReadSup;

TYPE
   VectEc = ARRAY[0..10] OF LONGINT;

VAR
	LeM, BestMina			        : MScal;
	valeurdea, fin, Debuta, Fina            : LONGINT;
	aaverifier, ecrit			: LONGINT;
	Lea					: MVect;
        Lem                                     : SuperInteger;
	LesI					: BVect;
	ListmMS1, Listr				: Factors;
	first					: BOOLEAN;
	PeriodeMax, Impair			: INTEGER;
	MinADate, Min, MinSurLesa		: LONGREAL;
	MinSucc			         	: LONGREAL;
	MT, MTMoySec, MTMinSec			: LONGREAL;
	LeK, DebutSucc, j			: INTEGER;
        ecart, BigT                             : VectEc;
	str1					: ARRAY [0..100] OF CHAR;
	Sorte, SorteMin, d, l, Dim		: LONGINT;
        MauvInd                                 : VectEc;
        TabA                                    : ARRAY [0..10] OF SuperInteger;


(* pour l'instant, MauvInd va nous rapporter les ecarts ou c'est *)
(* poche seulement si on appelle le programme pour un seul a*)
(* i.e, si on fait une recherche, pas clair qu'il va rapporter *)
(* les ecarts du a poche *)

(*-------------------------------------------------------------------*)
(*-----Procedure qui va lire dans un fichier comme "ProjGen.dat" le m*)
(*-----le k, le d maximal, et les bornes des dimensions entre -------*)
(*-----lesquelles on veut faire le test------------------------------*) 
(*-----PeriodeMax indique si on veut seulement regarder les "a" a ---*)
(*-----periode maximale et Impair indique si le m est impair ou non.-*)
(*-----ecrit=0: ecrit a l'ecran seulement les meilleurs a------------*)
(*-----ecrit=1: ecrit les res. intermediaires, pour chaque a---------*)
(*-----ecrit=2: ecrit les M_T pour chaque a--------------------------*)
(*-----ecrit=3: va ecrire M_T^min et M_T^moy dans MTmod.dat, qui ----*)
(*------------  lu par graph.m pour faire des histogrammes-----------*)
(*-----Donc, quand on fait recherche, utiliser ecrit=0; pour faire---*)
(*-----histogrammes, prendre ecrit=3, et pour verification, prendre--*)
(*-----ecrit=1 ou 2.-------------------------------------------------*)


(* Procedure qui lit le fichier d'entree, on lit en SuperInteger m et 
les a puisqu'un MRG combine sera represente par son equivalent non 
combine *)

PROCEDURE Lecture;
VAR
    comm :ARRAY [1..80] OF CHAR;
    l, i : LONGINT;

BEGIN
  OpenInput(".dat");
  
  (* valeur de m *)
  ReadLine(comm); ReadLn; 
  ReadSup(Lem,10); ReadLn;
  SupToMScal(Lem,LeM);

  (*ReadLongInt(Lem);ReadLn;
  LIToMScal(Lem, LeM);  *)
  
  (* Ordre du generateur *)
  ReadLine(comm); ReadLn; 
  ReadLongInt(LeK); ReadLn;

  (* Boucle sur l'ordre du generateur pour lire les a *)
  FOR i:= 0 TO (LeK -1) DO
     ReadLine(comm); ReadLn; 
     ReadSup(TabA[i],10);ReadLn;
  END; 
 
  (* Valeur de d *)
  ReadLine(comm); ReadLn;
  ReadLongInt(d); ReadLn;

  (* Valeur de BigT *)
  ReadLine(comm); ReadLn;
  FOR l:= 1 TO d DO
    ReadLongInt(BigT[l]);
  END;
  ReadLn;

  (* Fin, valeur de ecrit *)
  ReadLine(comm); ReadLn;
  ReadLongInt(ecrit); 

  CloseInput;

END Lecture;


(* Cette procedure ne devrait pas etre changee. *)

(*--------------------------------------------------------------------*)
(** Cette procedure sert a calculer le test spectral sur les indices  *)
(** non-successifs de facon recursive: elle est appelee dans la       *)
(** boucle principale apres avoir fait le test sur chaque paire       *)
(** (1,j), et calcule alors le test spectral sur les projections      *)
(** (1,j,l), pour l = j+1,...,BigT[3] etc., (1,j,l,m) pour            *)
(** j<l<m<BigT[4]  etc.                                               *)

PROCEDURE Testv(v : LONGINT; VAR step : VectEc; T: VectEc;
	        VAR TheI : BVect; a : MVect; VAR Minimum : LONGREAL;
		VAR Kind : LONGINT);
VAR
   i, Last, l : LONGINT;
   Mini, valeur : LONGREAL;
   DimCourante: LONGINT;

BEGIN

  Last := T[v];

  FOR l:= 1 TO v - 2 DO
    Last := Last - step[l];
  END;

  FOR i := 1 TO (Last - 1) DO
    step[v-1] := i;

    BAdd(TheI[v],BOne,TheI[v]);
    BAffect(TheI[v],TheI[v+1]);

    IF  (v = 5) THEN      
        WriteString("Indices : ");
        BWriteVect(TheI,v,3); WriteLn;WriteLn;
        (*LATBASIS.WriteBasis(MRG.Bas);*)
    END; 

    TestLa(a, TheI, MRG.Spectral, v, v, MRG.Verify0, MRG.None);

    Mini:=BASISLR.BConvLR(S2[v]);
    Mini := Sqrt(Mini);	
    IF (Mini < Minimum) THEN
      Minimum := Mini;
      Kind := v;
      MauvInd[v] := i;
      WriteLn;
      WriteString("---------------------------------------");WriteLn;
      WriteLongReal(Mini,3,12);WriteLn;
      WriteString("Dimension : ");
      WriteLongInt(v,3); WriteLn;
      WriteString("Indices : ");
      BWriteVect(TheI,v,3);
      WriteLn; WriteLn;
      valeur :=BASISLR.BConvLR(D2[v]);
      valeur := Sqrt(valeur);	
      WriteString("Distance entre les hyper plans "); WriteLn; 
      WriteLongReal(valeur,3,20); WriteLn;

      WriteString("Base: "); WriteLn; WriteLn;
      LATBASIS.WriteBasis(MRG.Bas);
      
    END;


    IF ( d > v) THEN
      Testv(v + 1, step, T, TheI, a, Minimum, Kind);
    END;

  END;
END Testv;


(*----------------  Programme principal  -------------------------------*)

VAR i : INTEGER;

BEGIN


(*----------------  Initialisation  ------------------------------------*)

  MCreateScal(LeM);
  MCreateScal(BestMina);
  ListmMS1 := NIL;
  Listr := NIL;
  first := TRUE;
  LatType := MRG.Full;
  MaxAllDim := TRUE;

  Create(Lem,3);
  FOR i:= 0 TO 10 DO
    Create(TabA[i],2);
  END;



(*------------------lecture du fichier d'entrees------------------*)
  Lecture;
  OpenOutput(".tmp");


  (* Initialisation du MRG avec le bon m, l'ordre k et la dimension max
     ou nous nous rendrons, soit BigT[1] *)
  InitMRG(LeM, LeK, BigT[1]);

  (* Si BigT[1] > 8 alors les bornes sont celles de Rogers *)
  IF (BigT[1] > 8) THEN
    InitREDBAS(BigT[1], REDBAS.Rogers);
  END;

  (* Create des vecteurs LesI[1..BigT[1]] et Lea[0..LeK] *)
  BCreateVect(LesI, 1, BigT[1] );
  MCreateVect(Lea, 0, LeK);

  (* Pas indice lacunaire au depart *)
  Lacunary := FALSE;

  (* Conversion de de donnees et ecriture dans le fichier *)

  WriteString("M: ");
  WriteSup(Lem,10,20); WriteLn; 

  FOR i:=1 TO LeK DO 
    SupToMScal(TabA[i-1], Lea[i]);  
    MWriteScal(Lea[i]); WriteString("  &  ");    
  END;
  WriteLn;


  (*---Calcul de S_t sur les sous-ensembles d'indices successifs-------*)
  (*---MinADate correspond a \tilde{M}_T^{min}-------------------------*)


  (* Test spectral de la dimension LeK+1 à la dimension BigT[1] *)
  Test(Lea,MRG.Spectral, LeK+1, BigT[1], MRG.Verify0, MRG.CurOut);


   WriteLn;WriteLn;WriteLn;WriteLn;WriteLn;WriteLn;WriteLn;WriteLn;WriteLn;

  (* Ceci sert à conserver le min de S_t jusqu'à présent *)
  
  MinADate:=BASISLR.BConvLR(S2[LeK+1]); 
  MinADate:= Sqrt(MinADate);
  Sorte := 1;
  MauvInd[1] := LeK+1;

  MinADate:=1.0;

  FOR i := (LeK+2) TO BigT[1] DO
    Min :=BASISLR.BConvLR(S2[i]); 
    Min := Sqrt(Min);
    IF (Min < MinADate) THEN
      MinADate := Min;
      Sorte := 1;
      MauvInd[1] := i;
      WriteLn;
      WriteString("---------------------------------------");WriteLn;
      WriteLongReal(Min,3,12);WriteLn;
      WriteString("Dimension : ");
      WriteLongInt(2,3); WriteLn;
    END;
  END;
  MT := MinADate;

  MinADate:=1.0;
  WriteString("Minimum venant du test spectral ordinaire:  ");
  WriteLongReal(MinADate,10,10);WriteLn;
 

  (* Création du vecteur d'indices lacunaires *)


  Lacunary := TRUE;
  BAffect(BZero, LesI[1]);
  BAffect(BZero, LesI[2]);

  (* Teste les doublets *)
  FOR Dim := 1 TO (BigT[2]-1) DO
    ecart[1] := Dim;
    BAdd(LesI[2], BOne, LesI[2]);
    BAffect(LesI[2], LesI[3]);

    (* Calcul du test spectral pour paires *)
    TestLa(Lea, LesI, MRG.Spectral, 2, 2, MRG.Verify0, MRG.None);

    Min := BASISLR.BConvLR(S2[2]);
    Min := Sqrt(Min);	
    IF (Min < MinADate) THEN
      MinADate := Min;
      Sorte := 2;
      MauvInd[2] := Dim;

      WriteLn;
      WriteString("---------------------------------------");WriteLn;
      WriteLongReal(Min,3,12);WriteLn;
      WriteString("Dimension : ");
      WriteLongInt(2,3); WriteLn;
      WriteString("Indices : ");
      BWriteVect(LesI,2,3);
    END;

    IF (d > 2) THEN
      Testv(3, ecart, BigT, LesI, Lea, MinADate, Sorte);
    END; 
  END;

  WriteLn;WriteLn;

  WriteString("Valeur minimale M_  ");
  WriteLongReal(MinADate,3,15);WriteLn;
  WriteString("Dimension:  ");  
  WriteLongInt(Sorte,3);WriteLn;
  
  CloseOutput;


END ProjGenLiMatin.













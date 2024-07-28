 
IMPLEMENTATION MODULE PALPHA;

(***************************************************************************

Environnement :  XDS Modula-2 sous SUN/Solaris et RedHat/Linux
-------------
Programmeur :   Renee Touzin
-----------
Module de base pour le calcul du P_alpha
***************************************************************************)


FROM MYINOUT  IMPORT WriteLn, WriteString, WriteCard, WriteInt, WriteBool,
                     WriteLongReal, ReadLn, ReadString, ReadCard, ReadInt,
                     ReadBool,WriteLongInt,ReadLongReal, ReadLongInt,
                     OpenInput, CloseInput, OpenOutput, CloseOutput,
                     OpenAsOutput, Error;
                    
(*FROM ulcg    IMPORT SetLCG;
FROM unif01   IMPORT Strip,StripLI;*)
FROM TABLES   IMPORT TabLR, CreateTab, DeleteTab, LR, LI, TabLI;
FROM NUM      IMPORT LIToLR, REALToLR, IToLI, Lg, Pow, IToLR,
                     Sqrt, ModLR, TwoExp, Trunc, MultModLI;              
FROM MULT     IMPORT MVect, MCreateVect, MScal, MCreateScal, LIToMScal,
                     SetFactors;
FROM SUPFACT  IMPORT Factors;
FROM MRG      IMPORT PerMax, InitMRG, DeleteMRG;
FROM MYSTR    IMPORT Append, Copy;
FROM WholeStr IMPORT IntToStr;
FROM SUPCONV  IMPORT IntToSup;
FROM SUPINT   IMPORT SuperInteger; 

CONST
       Pi = 3.1415926535897932;
       DeuxPi2 = 2.0*Pi*Pi;
       DeuxPi4 = DeuxPi2 *Pi*Pi;
       DeuxPi6 = DeuxPi4 *Pi*Pi;
       DeuxPi8 = DeuxPi6 *Pi*Pi;
       ConsAl4 = 1.0 + DeuxPi4/90.0;
       ConsAl6 = 1.0 + DeuxPi6/945.0;
       ConsAl8 = 1.0 + DeuxPi8/9450.0; 
       e = 2.718281828;
       UnSixieme = 1.0/6.0;
       MaxInt = 2147483647;

VAR
    WrGen : PROC;
    TitreGen : ARRAY [0..255] OF CHAR;
    Gen : Gener01;  
    U   : LONGREAL;
    Gen_Style : CARDINAL;
    M1, A1, C1, S1 : LONGINT;
    UnSurM1 : LONGREAL;
    k, q1, r1 : LONGINT;
    str : ARRAY [0..255] OF CHAR; 

(* Procedure provenant du module unif01 de testu01.  Sa presence ici est
pour eliminer tout lien entre latmrg et testu01                            *)
PROCEDURE Strip (r : LONGINT) : LONGREAL;
(* Retourne la valeur de Gen (), tronquee des r premiers bits.          *)
BEGIN
  IF r = 0 THEN  
     RETURN Gen () 
  END;
  U := Gen () * TwoExp [r];   
  RETURN (U - LFLOAT (TRUNC (U)))
END Strip;

(***************************************************************************)

(* Procedure provenant du module unif01 de testu01.  Sa presence ici est
pour eliminer tout lien entre latmrg et testu01                            *)
PROCEDURE StripLI (dr : LONGREAL; r : LONGINT) : LONGINT;
BEGIN
  IF r = 0 THEN 
    RETURN TRUNC (dr * Gen ()) 
  END;
  U := TwoExp [r] * Gen ();
  RETURN TRUNC (dr * (U - LFLOAT (TRUNC (U))))
END StripLI;

(***************************************************************************)
(* Provient de unif01 *)
PROCEDURE SetTitre (Titre : ARRAY OF CHAR);
BEGIN
  Copy (TitreGen, Titre);
END SetTitre;

(* Provient de unif01 *)
PROCEDURE AddTitreLI (S : ARRAY OF CHAR;  LI : LONGINT);
BEGIN
  Append (TitreGen, S);  IntToStr (LI, str);
  Append (TitreGen, str);
END AddTitreLI;

(**********************************************************************)

(* Provient de ulcg *)
PROCEDURE SetLCG ( m, a, c, s : LONGINT );
BEGIN
  IF ( (a < 0) OR (c < 0) OR (s < 0) OR
       (a >= m) OR (c >= m) OR (s >= m) ) THEN
    Error ("Parametre(s) incorrect(s), procedure ulcg.SetLCG")
  END;
  SetTitre ("SetLCG : ");  
  AddTitreLI (" m = ", m);
  AddTitreLI (", a = ", a);
  AddTitreLI (", c = ", c);  
  AddTitreLI (", s = ", s);
  WrGen := WrLCG;
  M1 := m;  A1 := a;  C1 := c;  S1 := s;
  UnSurM1 := 1.0 / LIToLR(m);

  (* Premier Cas *)
  IF ( m-1 <= (MaxInt - c) DIV a ) THEN        
    Gen_Style := 1;
    Gen := SmallLCG;
 
  ELSE
    q1 := m DIV a;  r1 := m MOD a;

    (* Second Cas *)
    IF ( r1 <= q1 ) THEN                      
      IF (c # 0) THEN
        Gen_Style := 2;  Gen := MediumLCG;
      ELSE
        Gen_Style := 3;  Gen := MediumMLCG;
      END;

    (* Troisieme Cas *)
    ELSE                                   
      Gen_Style := 4;
      Gen := LargeLCG;
    END
  END
END SetLCG;


(*********************************************************************)
(* Provient de ulcg *)
PROCEDURE SmallLCG () : LONGREAL;
(* Implantation utilisee lorsque (a*(m-1) + c) est representable     *)
(* comme LONGINT.                                                    *)
BEGIN
  S1 := ((A1 * S1) + C1) MOD M1;
  RETURN ( LFLOAT (S1) * UnSurM1 )
END SmallLCG;


(*********************************************************************)
(* Provient de ulcg *)
PROCEDURE MediumLCG () : LONGREAL;
(* Implantation utilisee lorsque a * (m MOD a) < m  et que c <> 0.   *)
BEGIN
  k := S1 DIV q1;
  S1 := A1 * (S1 - k * q1) - k * r1;
  IF (S1 < 0) THEN  
    S1 := S1 + C1  
  ELSE
    S1 := (S1 - M1) + C1 
  END;
  IF (S1 < 0) THEN 
    S1 := S1 + M1 
  END;
  RETURN ( LFLOAT (S1) * UnSurM1 )
END MediumLCG;

(***********************************************************************)
(* Provient de ulcg *)
PROCEDURE MediumMLCG () : LONGREAL;
(* Implantation utilisee lorsque a * (m MOD a) < m  et que c = 0.    *)
BEGIN
  k := S1 DIV q1;
  S1 := A1 * (S1 - k * q1) - k * r1;
  IF (S1 < 0) THEN 
    S1 := S1 + M1  END;
  RETURN ( LFLOAT (S1) * UnSurM1 )
END MediumMLCG;

(***********************************************************************)
(* Provient ulcg *)
PROCEDURE LargeLCG () : LONGREAL;
(* Implantation utilisee lorsqu'aucune des trois precedentes         *)
(* (SmallLCG, MediumMLCG, MediumLCG) ne peut l'etre.                 *)
BEGIN
  S1 := MultModLI (A1, S1, C1, M1);
  RETURN (LFLOAT (S1) * UnSurM1)
END LargeLCG;

(***************************************************************************)
(* Provient de ulcg *)
PROCEDURE WrLCG ();
BEGIN
  IF    Gen_Style = 1 THEN  WriteString (" small LCG")
  ELSIF Gen_Style = 2 THEN  WriteString (" medium LCG")
  ELSIF Gen_Style = 3 THEN  WriteString (" medium MLCG")
  ELSIF Gen_Style = 4 THEN  WriteString (" large LCG")
  END;
  WriteLn;
  WriteString ("  s = ");  WriteLongInt (S1, 1);  WriteLn
END WrLCG;


(***************************************************************************)
(* Lit le type de generateur, sert principalement d'entete au fichier *)
PROCEDURE ReadTypeGen(VAR TypeG : ARRAY OF CHAR);
BEGIN  
  ReadString(TypeG);
  ReadLn;
END ReadTypeGen;   


(***************************************************************************)
(* Lit le type de calcul a effectuer *)
PROCEDURE ReadTypeCalcul(VAR TypeC : ARRAY OF CHAR);
BEGIN  
  ReadString(TypeC);
  ReadLn;
END ReadTypeCalcul;


(***************************************************************************)
(* Lit le modulo de la recurrence *)
PROCEDURE ReadM(VAR M : INTEGER);
BEGIN
  ReadInt(M); 
  ReadLn;
END ReadM;


(***************************************************************************)
(* Lit les bornes a l'interieur desquelles un bon A(coefficient) doit*) 
(* etre trouve *)
PROCEDURE ReadBorneA(VAR InfA, SupA : LONGINT);
BEGIN
  ReadLongInt(InfA);
  ReadLongInt(SupA);
  ReadLn; 
END ReadBorneA;


(**************************************************************************)
(* Lit si le modulo est un nombre premier *)
PROCEDURE ReadPrime(VAR Prime : BOOLEAN);
BEGIN
  ReadBool(Prime);
  ReadLn;
END ReadPrime;


(**************************************************************************)
(* Lit le coefficient a de la recurrence *)
PROCEDURE ReadA(VAR A : INTEGER);
BEGIN
  ReadInt(A);
  ReadLn;
END ReadA;


(**************************************************************************)
(* Lit la plage de dimensions a parcourir *)
PROCEDURE ReadMinMax(VAR Min, Max, Saut : INTEGER);
BEGIN
  ReadInt(Min);
  ReadLn;
  ReadInt(Max);
  ReadLn;
  ReadInt(Saut);
  ReadLn;
END ReadMinMax;


(**************************************************************************)
(* Lit le alpha pour le calcul de P_/alpha *)
PROCEDURE ReadAlpha(VAR Alpha : INTEGER);
BEGIN
  ReadInt(Alpha);
  ReadLn;
END ReadAlpha;


(**************************************************************************)
(* Lit le booleen indiquant si la periode doit etre maximale *)
PROCEDURE ReadPeriodeMax(VAR PeriodeMax : BOOLEAN);
BEGIN
  ReadBool(PeriodeMax);  
  ReadLn;  
END ReadPeriodeMax;


(**************************************************************************)
PROCEDURE ReadSeed(VAR Seed : INTEGER);
BEGIN
  ReadInt(Seed);
  ReadLn;
END ReadSeed;


(**************************************************************************)
PROCEDURE ReadBeta(VAR Gen : CaractGenerateur);
VAR i : INTEGER;
BEGIN
  FOR i:= 0 TO Gen.Max DO
    ReadLongReal(Gen.TabBeta^[i]);
  END; 
  ReadLn;
END ReadBeta;


(**************************************************************************)
(*Procedure qui lit les caracteristiques du generateur dans le fichier*)
PROCEDURE SaisieDonnees(VAR Gen: CaractGenerateur);
  BEGIN
  ReadTypeGen(Gen.TypeGen);  
  ReadTypeCalcul(Gen.TypeCalcul);
  ReadM(Gen.M);
  ReadPrime(Gen.Prime);
  IF Gen.TypeCalcul[1] = "C" THEN
    ReadBorneA(Gen.BorneInfA, Gen.BorneSupA);
  ELSE
    ReadA(Gen.A);
    END;
  ReadMinMax(Gen.Min, Gen.Max, Gen.Saut);
  ReadAlpha(Gen.Alpha);
  ReadPeriodeMax(Gen.PeriodeMax); 
  ReadSeed(Gen.Seed);
  CreateTab(Gen.TabBeta, LR, Gen.Max +1);
  ReadBeta(Gen);
  END SaisieDonnees;


(***************************************************************************)

PROCEDURE PAlpha2s 
  (Gen    : CaractGenerateur;  
   S1, S2 : INTEGER;
   VAR P2 : ARRAY OF LONGREAL
  ); 
  (* Calcule P_2 en dimensions S1 a S2, en supposant que les poids sont 1. *)
  (* Les valeurs sont retournees dans P2[S1..S2].                          *)
  (* Le tableau P2 doit bien sur commencer a 0.                            *)

  VAR 
     FactReste, Modulo, OldMult, NewMult, Uij : LONGREAL;  
     i, j, s, PosTab  : INTEGER;
     M, A, Seed, C    : LONGINT; 
     T, Mult, Reste   : ARRAY [0..MaxDim] OF LONGREAL;
  BEGIN
  IF S2 > MaxDim THEN
     Error (" CalculAllPAlpha2 called with S2 > MaxDim.");
     END;

  (* Initialisation *)
  Mult[0] := 1.0;   Reste[0] := 1.0;
  M := IToLI (Gen.M);  A := IToLI(Gen.A);
  Seed := IToLI (Gen.Seed);
  Modulo := IToLR (Gen.M);
  C := 0                              ;  (* !!! *)
  SetLCG (M, A, C, Seed);

  FOR j:= 0 TO S2-1 DO
     Uij  := Strip (0);
     T[j] := 1.0 + DeuxPi2 * (UnSixieme + Uij * (Uij-1.0)); 
     END;
  Mult[0] := 1.0;    Reste[0] := 1.0;
  FactReste := 1.0 + DeuxPi2 * UnSixieme;
  FOR s := 1 TO S2 DO
     Mult[s]  := Mult[s-1] * T[S2-s];
     P2[s]    := Mult[s];
     Reste[s] := Reste[s-1] * FactReste;
     END;

  FOR i := 0 TO Gen.M - 3 DO
     Uij := Strip (0);
     NewMult := 1.0 + DeuxPi2 * (UnSixieme + Uij * (Uij-1.0)); 
     FOR s := S1 TO S2 DO
        PosTab := (i-s) MOD S2;
        OldMult := T[PosTab];
        Mult[s] := Mult[s] * NewMult / OldMult;  
        P2[s]   := P2[s] + Mult[s];
        END;
     T[PosTab] := NewMult;
     END; 
  FOR s := S1 TO S2 DO
     P2[s] := ((P2[s] + Reste[s]) / Modulo) - 1.0;
     END;
  END PAlpha2s;

(***************************************************************************)

PROCEDURE CalculPAlpha2 (Gen : CaractGenerateur;  S: INTEGER; 
                         PtrTabUij : TabLR ): LONGREAL;
   (* Procedure qui calcule le P_Alpha(2).  *)
  VAR 
     Mult, Add, Reste, Modulo, OldMult, NewMult, Uij : LONGREAL;  
     i, j, PosTab  : INTEGER;
     M, A, Seed, C : LONGINT; 
     (*  TabBetaCarre  : TabLR;  *)
     T, TBeta2     : ARRAY [0..MaxDim] OF LONGREAL;
  BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A);
  Seed := IToLI(Gen.Seed);
  C := 0;
  Reste := 1.0;
  Modulo := IToLR(Gen.M); 
  SetLCG(M, A, C, Seed);
  (*  CreateTab (TabBetaCarre, LR, S+1);  *)

  FOR j:= 0 TO S-1 DO
    Uij := Strip(0);
    TBeta2[j+1] := Gen.TabBeta^[j+1] * Gen.TabBeta^[j+1];
    T[j] := 1.0 + DeuxPi2 * TBeta2[j+1] * (UnSixieme + Uij*(Uij-1.0)); 
    Mult  :=  Mult * T[j];
    Reste := Reste * (1.0 + DeuxPi2 * TBeta2[j+1] * UnSixieme);     
    END;
  Add := Add + Mult; 
  FOR i := 0 TO Gen.M - 3 DO
    PosTab := i MOD S;   
    Uij := Strip(0);
    NewMult := 1.0 + DeuxPi2 * TBeta2 [PosTab+1]
               * (UnSixieme + Uij * (Uij-1.0)); 
    OldMult := T[PosTab];
    T[PosTab] := NewMult;
    Mult := Mult * NewMult / OldMult;  
    Add := Add + Mult;  
    END; 
  Add := (((Add + Reste)/Modulo) - 1.0) * Gen.TabBeta^[0];  
  (*  DeleteTab (TabBetaCarre, LR, S+1);  *)
  RETURN Add;
  END CalculPAlpha2;


(**************************************************************************)

PROCEDURE PAlpha2PerNonMaxs
  (Gen    : CaractGenerateur;  
   S1, S2 : INTEGER;
   VAR P2 : ARRAY OF LONGREAL
  ); 
  (* Calcule P_2 en dimensions S1 a S2, en supposant que les poids sont 1. *)
  (* Les valeurs sont retournees dans P2[S1..S2].                          *)
  (* Le tableau P2 doit bien sur commencer a 0.                            *)

  VAR 
     Modulo, InvModulo, Prod, Uij : LONGREAL;  
     j, s    : INTEGER;
     M, A    : LONGINT; 
     Ind, Puis : ARRAY [0..MaxDim] OF LONGINT;
     T       : TabLR;
  BEGIN
  IF S2 > MaxDim THEN
     Error (" CalculAllPAlpha2 called with S2 > MaxDim.");
     END;

  (* Initialisation *)
  M := IToLI (Gen.M);  A := IToLI(Gen.A);
  Modulo := IToLR (Gen.M);   
  InvModulo := 1.0 / Modulo;
  CreateTab (T, LR, M);
  FOR j := 0 TO M-1 DO
     Uij  := VAL (LONGREAL, j) * InvModulo;
     T^[j] := 1.0 + DeuxPi2 * (UnSixieme + Uij * (Uij-1.0)); 
     END;
  Puis[0] := 1;
  FOR s := 1 TO S2 DO
     Puis[s] := MultModLI (Puis[s-1], A, 0, M);  (* = A^s mod M  *)
     Ind[s]  := 0;
     END;
  FOR j := 0 TO M-1 DO
     Prod := 1.0;
     FOR s := 1 TO S2 DO
        Prod  := Prod * T^[Ind[s]];
        P2[s] := P2[s] + Prod;
        Ind[s] := (Ind[s] + Puis[s]) MOD M;
        END;
     END; 
  FOR s := S1 TO S2 DO
     P2[s] := P2[s] / Modulo - 1.0;
     END;
  DeleteTab (T, LR, M);
  END PAlpha2PerNonMaxs;

(**************************************************************************)

PROCEDURE PAlpha2PerNonMax(Gen: CaractGenerateur; S: INTEGER): LONGREAL;
  (* Procedure qui calcule le P_Alpha(2).  *)
VAR 
  Mult, Add, Reste, Modulo, Uij : LONGREAL;    
  i, j, k : INTEGER;
  M, A : LONGINT; 
  Vect, VectTemp : TabLI;
  TabBetaCarre : TabLR;

BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A); 
  Modulo := IToLR(Gen.M);  
  CreateTab(TabBetaCarre, LR, S+1);
  CreateTab(Vect, LI, S);
  CreateTab(VectTemp, LI, S);
  
  (*Tableau contenant le vecteur des points*)
  Vect^[0] := 1; VectTemp^[0] := 1;
  TabBetaCarre^[1] := Gen.TabBeta^[1] * Gen.TabBeta^[1];
  Reste := (1.0 + DeuxPi2 * TabBetaCarre^[1]/6.0);
  FOR i:=1  TO S-1 DO
    Vect^[i] := MultModLI (Vect^[i-1], A, 0, M);
    VectTemp^[i] := Vect^[i]; 
    TabBetaCarre^[i+1] := Gen.TabBeta^[i+1] * Gen.TabBeta^[i+1];
    Reste := Reste * (1.0 + ((DeuxPi2 * TabBetaCarre^[i+1])/6.0));
  END;

  (* Calcul du P_alpha*)
  FOR i:= 1 TO M-1 DO
    Mult := 1.0;
    FOR j:= 0 TO S-1 DO
       Uij := LIToLR(VectTemp^[j])/Modulo;   
      Mult  :=  Mult * (1.0 + DeuxPi2*TabBetaCarre^[j+1]*(UnSixieme + Uij*(Uij-1.0)));      
    END;
    Add := Add + Mult;
    FOR k:= 0 TO S-1 DO      
      VectTemp^[k] := (VectTemp^[k] + Vect^[k]) MOD M;      
    END;    
  END;   
  Add := (((Add + Reste)/Modulo) - 1.0)* Gen.TabBeta^[0];  
  DeleteTab(TabBetaCarre, LR, S+1);
  DeleteTab(Vect, LI, S);
  DeleteTab(VectTemp, LI, S);
  RETURN Add;
END PAlpha2PerNonMax;


(**************************************************************************)
PROCEDURE CalculPAlpha4(Gen: CaractGenerateur; S: INTEGER; PtrTabUij : TabLR): LONGREAL;
VAR 
  Mult, Add, Modulo, Reste, OldMult : LONGREAL;  
  Uij, Uij2, Uij4, Uij3 : LONGREAL;
  i, j, PosTab : INTEGER;  
  M, A, Seed, C : LONGINT; 
  TabBeta4 : TabLR;
BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A);
  Seed := IToLI(Gen.Seed);
  C := 0;
  Reste := 1.0;
  Modulo := REALToLR(FLOAT(Gen.M));
  (* CALCULS *) 
  SetLCG(M, A, C, Seed); 
  CreateTab(TabBeta4, LR, S+1);

  FOR j:= 0 TO S-1 DO
    Uij := Strip(0);    
    Uij2 := Uij * Uij;
    Uij3 := Uij2* Uij;
    Uij4 := Uij2 * Uij2;
    TabBeta4^[j+1]:= Gen.TabBeta^[j] * Gen.TabBeta^[j];
    TabBeta4^[j+1]:= TabBeta4^[j+1] * TabBeta4^[j+1];
    PtrTabUij^[j] := (1.0 - (DeuxPi4*TabBeta4^[j+1]/3.0)*
                                 (Uij4 - 2.0*Uij3 + Uij2 - 1.0/30.0));
    Mult  := Mult * PtrTabUij^[j];    
    Reste := Reste * (1.0 + DeuxPi4 *TabBeta4^[j+1]/90.0) ; (*1 + 2Pi^4/90*)    
  END;
  Add := Add + Mult;
  FOR i := 1 TO Gen.M - 2 DO
    PosTab := (i-1) MOD S;
    Uij := Strip(0);     
    Uij2 := Uij * Uij;
    Uij3 := Uij2 * Uij;
    Uij4 := Uij2 * Uij2;
    OldMult := PtrTabUij^[PosTab];
    PtrTabUij^[PosTab]:= (1.0 - (DeuxPi4*TabBeta4^[PosTab]/3.0)*
                                     (Uij4 - 2.0*Uij3 + Uij2 - 1.0/30.0)); 
    Mult := (Mult * PtrTabUij^[PosTab])/OldMult;
    Add := Add + Mult; 
  END; 
  Add := (((Add + Reste)/Modulo) - 1.0) *Gen.TabBeta^[0]; 
  DeleteTab(TabBeta4, LR, S+1);
  RETURN Add;
END CalculPAlpha4;


(**************************************************************************)
(*Procedure qui calcule le P_Alpha(2)*)
PROCEDURE PAlpha4PerNonMax(Gen: CaractGenerateur; S: INTEGER): LONGREAL;
VAR 
  Mult, Add, Reste, Modulo : LONGREAL;   
  Uij, Uij2, Uij4, Uij3 : LONGREAL;
  i, j, k : INTEGER;
  M, A : LONGINT;
  Temp : LONGREAL;
  Vect, VectTemp : TabLI;
  TabBeta4 : TabLR;

BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A); 
  Modulo := IToLR(Gen.M);  
  CreateTab(TabBeta4, LR, S+1);
  CreateTab(Vect, LI, S);
  CreateTab(VectTemp, LI, S);
  
  (*Tableau contenant le vecteur des points*)
  Vect^[0] := 1; VectTemp^[0] := 1;
  TabBeta4^[1] := Gen.TabBeta^[1] * Gen.TabBeta^[1];
  TabBeta4^[1] := TabBeta4^[1] * TabBeta4^[1];
  Reste := (1.0 + DeuxPi4 *TabBeta4^[1]/90.0);
  FOR i:=1  TO S-1 DO
    Temp := LIToLR(Vect^[i-1]*A);
    Vect^[i] := Trunc(ModLR(Temp, Modulo));
    VectTemp^[i] := Vect^[i];
    TabBeta4^[i+1] := Gen.TabBeta^[i+1] * Gen.TabBeta^[i+1];
    TabBeta4^[i+1] := TabBeta4^[i+1] * TabBeta4^[i+1];
    Reste := Reste * (1.0 + DeuxPi4 *TabBeta4^[i+1]/90.0);
  END;

  (* Calcul du P_alpha*)
  FOR i:= 1 TO M-1 DO
    Mult := 1.0;
    FOR j:= 0 TO S-1 DO
      Uij := LIToLR(VectTemp^[j])/Modulo;    
      Uij2 := Uij * Uij;
      Uij3 := Uij2* Uij;
      Uij4 := Uij2 * Uij2;
      Mult  :=  Mult * (1.0 - (DeuxPi4 * TabBeta4^[j+1]/3.0)*
                                   (Uij4 - 2.0*Uij3 + Uij2 - 1.0/30.0)); 
    END;
    Add := Add + Mult;
    FOR k:= 0 TO S-1 DO      
      VectTemp^[k] := (Vect^[k] + VectTemp^[k]) MOD M;      
    END;    
  END;  
 
  Add := (((Add + Reste)/Modulo) - 1.0)* Gen.TabBeta^[0];  
  DeleteTab(TabBeta4, LR, S+1);
  DeleteTab(Vect, LI, S);
  DeleteTab(VectTemp, LI, S);
  RETURN Add;
END PAlpha4PerNonMax;


(**************************************************************************)
PROCEDURE CalculPAlpha6(Gen: CaractGenerateur; S: INTEGER; PtrTabUij : TabLR): LONGREAL;
VAR 
  Mult, Add, Reste, OldMult, Modulo : LONGREAL;
  Uij, Uij2, Uij4, Uij5, Uij6 : LONGREAL;  
  i, j, PosTab : INTEGER;  
  M, A, Seed, C : LONGINT; 
  TabBeta6 : TabLR;
BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A);
  Seed := IToLI(Gen.Seed);
  C := 0;
  Reste := 1.0;
  Modulo := REALToLR(FLOAT(Gen.M)); 
  SetLCG(M, A, C, Seed);
  CreateTab(TabBeta6, LR, S+1);
 
  FOR j:= 0 TO S-1 DO
    Uij := Strip(0);    
    Uij2 := Uij * Uij;
    Uij4 := Uij2 * Uij2;
    Uij5 := Uij4 * Uij;  
    Uij6 := Uij4 * Uij2;
    TabBeta6^[j+1] := Gen.TabBeta^[j+1] * Gen.TabBeta^[j+1];
    TabBeta6^[j+1] := Gen.TabBeta^[j+1] * TabBeta6^[j+1];
    TabBeta6^[j+1] := TabBeta6^[j+1] * TabBeta6^[j+1];
    PtrTabUij^[j] := (1.0 + 2.0*DeuxPi6*TabBeta6^[j+1]/45.0 * 
                               (Uij6 - 3.0*Uij5 + 2.5*Uij4 - 0.5*Uij2 + 1.0/42.0));
    Mult  :=  Mult * PtrTabUij^[j];
    Reste := Reste * (1.0 + DeuxPi6 *TabBeta6^[j+1]/ 945.0); 
  END;
  Add := Add + Mult;
  FOR i := 1 TO Gen.M - 2 DO
    PosTab := (i-1) MOD S;   
    Uij := Strip(0);
    Uij2 := Uij * Uij;
    Uij4 := Uij2 * Uij2;
    Uij5 := Uij4 * Uij;  
    Uij6 := Uij4 * Uij2;
    OldMult := PtrTabUij^[PosTab];
    PtrTabUij^[PosTab] := (1.0 + 2.0*DeuxPi6* TabBeta6^[PosTab]/45.0 * 
                               (Uij6 - 3.0*Uij5 + 2.5*Uij4 - 0.5*Uij2 + 1.0/42.0));
    Mult := (Mult * PtrTabUij^[PosTab])/OldMult;   
    Add := Add + Mult; 
  END;
  Add := (((Add + Reste)/Modulo) - 1.0)* Gen.TabBeta^[0]; 
  DeleteTab(TabBeta6, LR, S+1);
  RETURN Add;
END CalculPAlpha6;


(*************************************************************************)
(*Procedure qui calcule le P_Alpha(2)*)
PROCEDURE PAlpha6PerNonMax(Gen: CaractGenerateur; S: INTEGER): LONGREAL;
VAR 
  Mult, Add, Reste, Modulo : LONGREAL;  
  Uij, Uij2, Uij4, Uij5, Uij6 : LONGREAL;  
  i, j, k : INTEGER;
  M, A : LONGINT; 
  Vect, VectTemp : TabLI;
  TabBeta6 : TabLR;
  Temp : LONGREAL;

BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A); 
  Modulo := IToLR(Gen.M);  
  CreateTab(TabBeta6, LR, S+1);
  CreateTab(Vect, LI, S);
  CreateTab(VectTemp, LI, S);
  
  (*Tableau contenant le vecteur des points*)
  Vect^[0] := 1; VectTemp^[0] := 1;
  TabBeta6^[1] := Gen.TabBeta^[1] * Gen.TabBeta^[1];
  Reste := (1.0 + DeuxPi6 *TabBeta6^[1]/ 945.0); 
  FOR i:=1  TO S-1 DO
    Temp := LIToLR(Vect^[i-1]*A);
    Vect^[i] := Trunc(ModLR(Temp, Modulo));
    VectTemp^[i] := Vect^[i];
    TabBeta6^[i+1] := Gen.TabBeta^[i+1] * Gen.TabBeta^[i+1];
    TabBeta6^[i+1] := Gen.TabBeta^[i+1] * TabBeta6^[i+1];
    TabBeta6^[i+1] := TabBeta6^[i+1] * TabBeta6^[i+1];
    Reste := Reste * (1.0 + DeuxPi6 *TabBeta6^[i+1]/ 945.0); 
  END;

  (* Calcul du P_alpha*)
  FOR i:= 1 TO M-1 DO
    Mult := 1.0;
    FOR j:= 0 TO S-1 DO
      Uij := LIToLR(VectTemp^[j])/Modulo; 
      Uij2 := Uij * Uij;
      Uij4 := Uij2 * Uij2;
      Uij5 := Uij4 * Uij;  
      Uij6 := Uij4 * Uij2;
      Mult  :=  Mult * (1.0 + 2.0*DeuxPi6 * TabBeta6^[j+1]/45.0*
                             (Uij6 - 3.0*Uij5 + 2.5*Uij4 - 0.5*Uij2 + 1.0/42.0));
    END;
    Add := Add + Mult;
    FOR k:= 0 TO S-1 DO      
      VectTemp^[k] := (Vect^[k] + VectTemp^[k]) MOD M;      
    END;    
  END;  
 
  Add := (((Add + Reste)/Modulo) - 1.0)* Gen.TabBeta^[0];  
  DeleteTab(TabBeta6, LR, S+1);
  DeleteTab(Vect, LI, S);
  DeleteTab(VectTemp, LI, S);
  RETURN Add;
END PAlpha6PerNonMax;


(**************************************************************************)
PROCEDURE CalculPAlpha8(Gen: CaractGenerateur; S: INTEGER; PtrTabUij : TabLR): LONGREAL;
VAR 
  Mult, Add, Reste, Modulo, OldMult : LONGREAL;  
  Uij, Uij2, Uij4, Uij6, Uij7, Uij8 : LONGREAL; 
  i, j, PosTab : INTEGER;
  M, A, Seed, C : LONGINT; 
  TabBeta8 : TabLR;

BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A);
  Seed := IToLI(Gen.Seed);
  C := 0;
  Reste := 1.0;
  Modulo := REALToLR(FLOAT(Gen.M)); 
  SetLCG(M, A, C, Seed);
  CreateTab(TabBeta8, LR, S+1);
  FOR j:= 0 TO S-1 DO
    Uij := Strip(0);     
    Uij2 := Uij * Uij;
    Uij4 := Uij2 * Uij2;
    Uij6 := Uij2 * Uij4;
    Uij7 := Uij6 * Uij;
    Uij8 := Uij4 * Uij4;  
    TabBeta8^[j+1] := Gen.TabBeta^[j+1] * Gen.TabBeta^[j+1];
    TabBeta8^[j+1] := TabBeta8^[j+1] * TabBeta8^[j+1];
    TabBeta8^[j+1] := TabBeta8^[j+1] * TabBeta8^[j+1];   
    PtrTabUij^[j] := (1.0 - (DeuxPi8*TabBeta8^[j+1]/315.0) * (Uij8 - 4.0*Uij7 + (14.0/3.0)*Uij6
                                             - (7.0/3.0)*Uij4 + (2.0/3.0)*Uij2 - 1.0/30.0));
    Mult  :=  Mult * PtrTabUij^[j]; 
    Reste := Reste * (1.0 + DeuxPi8*TabBeta8^[j+1]/9450.0); 
  END;
  Add := Add + Mult;
  FOR i := 1 TO Gen.M - 2 DO
    PosTab := (i-1) MOD S;
    Uij := Strip(0);   
    Uij2 := Uij * Uij;
    Uij4 := Uij2 * Uij2;
    Uij6 := Uij2 * Uij4;
    Uij7 := Uij6 * Uij;
    Uij8 := Uij4 * Uij4;
    OldMult := PtrTabUij^[PosTab];
    PtrTabUij^[PosTab] := (1.0 - (DeuxPi8*TabBeta8^[PosTab+1]/315.0) * (Uij8 - 4.0*Uij7 + (14.0/3.0)*Uij6
                                             - (7.0/3.0)*Uij4 + (2.0/3.0)*Uij2 - 1.0/30.0));
    Mult := (Mult * PtrTabUij^[PosTab]) / OldMult;                     
    Add := Add + Mult; 
  END;
  Add := (((Add + Reste)/Modulo) - 1.0)*Gen.TabBeta^[0]; 
  DeleteTab(TabBeta8, LR, S+1);
  RETURN Add;
END CalculPAlpha8;


(**************************************************************************)
(*Procedure qui calcule le P_Alpha(2)*)
PROCEDURE PAlpha8PerNonMax(Gen: CaractGenerateur; S: INTEGER): LONGREAL;
VAR 
  Mult, Add, Reste, Modulo : LONGREAL;  
  Uij, Uij2, Uij4, Uij6, Uij7, Uij8 : LONGREAL; 
  i, j, k : INTEGER;
  M, A : LONGINT; 
  Vect, VectTemp : TabLI;
  TabBeta8 : TabLR;
  Temp : LONGREAL;

BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A); 
  Modulo := IToLR(Gen.M);  
  CreateTab(TabBeta8, LR, S+1);
  CreateTab(Vect, LI, S);
  CreateTab(VectTemp, LI, S);
  
  (*Tableau contenant le vecteur des points*)
  Vect^[0] := 1; VectTemp^[0] := 1;
  TabBeta8^[1] := Gen.TabBeta^[1] * Gen.TabBeta^[1];
  Reste := 1.0 + DeuxPi8* TabBeta8^[1]/9450.0; 
  FOR i:=1  TO S-1 DO
    Temp := LIToLR(Vect^[i-1]*A);
    Vect^[i] := Trunc(ModLR(Temp, Modulo));  
    VectTemp^[i] := Vect^[i];
    TabBeta8^[i+1] := Gen.TabBeta^[i+1] * Gen.TabBeta^[i+1];
    TabBeta8^[i+1] := TabBeta8^[i+1] * TabBeta8^[i+1];
    TabBeta8^[i+1] := TabBeta8^[i+1] * TabBeta8^[i+1];
    Reste := Reste * (1.0 + DeuxPi8* TabBeta8^[i+1]/9450.0); 
  END;

  (* Calcul du P_alpha*)
  FOR i:= 1 TO M-1 DO
    Mult := 1.0;
    FOR j:= 0 TO S-1 DO
      Uij := LIToLR(VectTemp^[j])/Modulo;    
      Uij2 := Uij * Uij;
      Uij4 := Uij2 * Uij2;
      Uij6 := Uij2 * Uij4;
      Uij7 := Uij6 * Uij;
      Uij8 := Uij4 * Uij4;
      Mult  :=  Mult * (1.0 - DeuxPi8 * TabBeta8^[j+1]/315.0 * (Uij8 - 4.0*Uij7 + (14.0/3.0)*Uij6
                                             - (7.0/3.0)*Uij4 + (2.0/3.0)*Uij2 - 1.0/30.0));      
    END;
    Add := Add + Mult;
    FOR k:= 0 TO S-1 DO      
      VectTemp^[k] := (Vect^[k] + VectTemp^[k]) MOD M;      
    END;    
  END;  
 
  Add := (((Add + Reste)/Modulo) - 1.0)* Gen.TabBeta^[0];  
  DeleteTab(TabBeta8, LR, S+1);
  DeleteTab(Vect, LI, S);
  DeleteTab(VectTemp, LI, S);
  RETURN Add;
END PAlpha8PerNonMax;


(************************************************************************)
PROCEDURE CalculBAlpha2(Gen: CaractGenerateur; S: INTEGER): LONGREAL;
VAR
  Term1, Term2 : LONGREAL;
  Mult1, Mult2 : LONGREAL;
  Modulo, Dim : LONGREAL;
  i : INTEGER;
BEGIN
  Modulo := REALToLR(FLOAT(Gen.M));
  Dim := REALToLR(FLOAT(S));
  Term1 := (e*e/(Dim*Dim));
  Term2 := (2.0 * Lg(Modulo)*0.301029995 + Dim)*(0.602059991 * Lg(Modulo) + Dim);
  Mult1 := 1.0;
  Mult2 := 1.0;
  FOR i := 1 TO S DO
    Mult1 := Mult1 * Term1;
    Mult2 := Mult2 * Term2;
  END; 
  Term1 := Mult1 * Mult2/ (Modulo * Modulo);
  RETURN Term1; 
END CalculBAlpha2;


(*************************************************************************)
(*Verifie si la periode du generateur contenu dans Gen est maximale*)
PROCEDURE PeriodeMax(Gen : CaractGenerateur): BOOLEAN;
VAR List1, List2 : Factors;
    TabVect : MVect;
    A,M : MScal; 
BEGIN   
  MCreateVect(TabVect,1,1);
  MCreateScal(A);
  LIToMScal (IToLI(Gen.A),A);
  TabVect[1]:= A;   
  MCreateScal(M);
  LIToMScal(IToLI(Gen.M), M);
  List1 := NIL;
  List2 := NIL;
  InitMRG(M,1,1);
  SetFactors(List1, List2, 1);  
  DeleteMRG(1);    
  RETURN PerMax(TabVect, List1, List2);  
END PeriodeMax; 


(**************************************************************************)
(*Ecrit les donnees definissant le generateur dans le fichier de sortie*)
PROCEDURE EcritDonnees(Gen : CaractGenerateur);
BEGIN
  WriteLn;
  WriteString(" \noindent");WriteLn;
  WriteString(" CALCUL DU ");
  WriteString(Gen.TypeCalcul);
  WriteString(" \\"); 
  WriteLn;
  WriteLn;
  WriteString(" DONNEES");WriteString("\\");
  WriteLn;
  WriteString("--------------------------------------------------------"); 
  WriteString(" \\ \\"); 
  WriteLn; 
  WriteString(" Type de Generateur :                     ");
  WriteString(Gen.TypeGen);
  WriteString(" \\");
  WriteLn;
  WriteString(" Modulo (m):                            ");
  WriteInt(Gen.M,5);
  WriteString(" \\");
  WriteLn;
  IF Gen.TypeCalcul[1] <> "C" THEN
    WriteString(" Multiplicateur (a):                   ");
    WriteInt(Gen.A,5);
    WriteString(" \\");
    WriteLn;
  ELSE 
    WriteString(" Borne inferieure du multiplicateur (a):");
    WriteInt(Gen.BorneInfA,5);
    WriteString(" \\");
    WriteLn;
    WriteString(" Borne superieure du multiplicateur (a):");
    WriteInt(Gen.BorneSupA,5);
    WriteString(" \\");
    WriteLn;
  END;
  WriteString(" Dimension minimale:                    "); 
  WriteInt(Gen.Min,5);
  WriteString(" \\");
  WriteLn;
  WriteString(" Dimension maximale:                    "); 
  WriteInt(Gen.Max,5);
  WriteString(" \\"); 
  WriteLn;
  WriteString(" Saut entre les dimensions : ");
  WriteInt(Gen.Saut,5);
  WriteString(" \\"); 
  WriteLn;
  WriteString(" Alpha:                                 "); 
  WriteInt(Gen.Alpha,5);
  WriteString(" \\");
  WriteLn;
  WriteString(" Seed du generateur:                    ");
  WriteInt(Gen.Seed,5);
  WriteString(" \\");
  WriteLn;
  WriteString(" Verification de la periode maximale:   "); 
  WriteBool(Gen.PeriodeMax);
  WriteString(" \\ ");
  WriteLn;
  WriteLn;
  WriteLn;
  WriteLn;
  WriteString(" RESULTATS ");WriteString("\\ ");
  WriteLn;
  WriteString("--------------------------------------------------------"); 
  WriteString(" \\ \\ ");
  WriteLn;
END EcritDonnees;


(*************************************************************************)
(* Ecrit l'entete du fichier latex *)
PROCEDURE EcritEntete;
BEGIN
  WriteString("\documentclass[12pt]{article}");
  WriteLn;
  WriteString("\usepackage{amsmath}");
  WriteLn;
  WriteString("\textwidth=6in");
  WriteLn;
  WriteString("\textheight=8in");
  WriteLn;
  WriteString("\topmargin=-.5cm");
  WriteLn;
  WriteString("\oddsidemargin=0.5cm");
  WriteLn;
  WriteString("\parindent=35pt");
  WriteLn;
  WriteString("\parskip=8pt plus 1pt minus 1pt");
  WriteLn;
  WriteLn;
  WriteString("\begin{document}");
END EcritEntete;


(**************************************************************************)
(* Ecrit le resultat du calcul effectue soit PAlpha ou BAlpha*)
PROCEDURE EcritPBAlpha(PBAlpha:LONGREAL; Dim:INTEGER; Gen: CaractGenerateur);
BEGIN
  WriteString(" En dimension ");
  WriteInt(Dim,2);
  WriteString(" le ");
  WriteString(Gen.TypeCalcul);
  WriteString(" est de:  ");
  WriteLongReal(PBAlpha,5,5);
  WriteString("\\");
  WriteLn;
END EcritPBAlpha;


(**************************************************************************)
(* Procedure qui met des zeros a tous les elements du tableau*)
PROCEDURE InitTab(Tab : TabLR; Dim : INTEGER);
VAR i : INTEGER;
BEGIN
  FOR i := 0 TO Dim-1 DO
    Tab^[i] := 0.0;
  END;
END InitTab;


(**************************************************************************)
(* Calcule la moyenne des PAlphas contenu dans un tableau*)
PROCEDURE Moyenne(Tab : TabLR; Debut, Fin : INTEGER): LONGREAL;
VAR Total : LONGREAL;
    i : INTEGER;
BEGIN
  Total := 0.0;
  FOR i := Debut TO Fin DO
    Total:= Total + Tab^[i];
  END;
  RETURN (Total/IToLR(Fin-Debut+1)); 
END Moyenne;


(**************************************************************************)
(* Calcule l'ecart-type des PAlphas contenu dans un tableau*)
PROCEDURE EcartType(Tab : TabLR; Debut, Fin : INTEGER) : LONGREAL;
VAR i : INTEGER;
    TotalX, TotalXCarre : LONGREAL;
    Ecart : LONGREAL;
BEGIN
    TotalX := 0.0;
    TotalXCarre := 0.0;
  FOR i:= Debut TO Fin DO
    TotalX := TotalX + Tab^[i];  
    TotalXCarre := TotalXCarre + (Tab^[i] * Tab^[i]);
  END;
  TotalX := TotalX*TotalX/ IToLR(Fin- Debut +1);
  Ecart := (TotalXCarre-TotalX)/IToLR(Fin-Debut);  
  RETURN Sqrt(Ecart);
END EcartType;

(**************************************************************************)
(* Procedure qui trie un tableau en utilisant un bubble sort *)
PROCEDURE SortTab(Tab : TabLR; Dim : INTEGER);
VAR i, j : INTEGER;
    Bidon : LONGREAL;
BEGIN
  FOR i := 0 TO Dim-1 DO
    FOR j := 0 TO Dim-1-i DO
      IF Tab^[j] > Tab^[j+1] THEN
        Bidon := Tab^[j];
        Tab^[j] := Tab^[j+1];
        Tab^[j+1] := Bidon;
      END;
    END;
  END;
END SortTab;


(*************************************************************************)
(* Procedure qui separe en intervalle les donnees d'un tableau *)
PROCEDURE MakeInterv(TabPAl : TabLR; Dim : INTEGER);
VAR Min, Max, Ecart : LONGREAL;
    PosMin, PosMax : INTEGER;
    i,j,PosPAl,PosEcart : INTEGER;
    TabEcart: TabLR;
    TabQtte: TabLI;
    NbInter: INTEGER;
    StdDev, Mean : LONGREAL;
BEGIN
  NbInter := 50;
  (*Trouve le min car il y a des zeros au debut du tableau*)
  i := 0;
  WHILE TabPAl^[i]= 0.0 DO
    i := i +1;
  END;
  PosPAl := i;

  (* Calcul de l'ecart-type et de la moyenne *)
  StdDev := EcartType(TabPAl, PosPAl, Dim);
  Mean := Moyenne(TabPAl, PosPAl, Dim);
  
  (* Calcul du depart et de la fin des donnees incluses dans le graphe*)
  (* selon l'ecart-type et la moyenne *)
  i:= PosPAl;
  WHILE TabPAl^[i] < Mean - 0.45 * StdDev DO
    i:= i +1;
  END;
  PosMin := i;
  Min := TabPAl^[i];
  i := Dim;
  WHILE TabPAl^[i] > Mean + 0.45 * StdDev DO
    i:= i - 1;
  END;
  PosMax := i;
  Max := TabPAl^[i];

  (* Si on veut toutes les valeurs*)
  (* PosMin := PosPAl;  Min := TabPAl^[PosMin];*)
  (* PosMax := Dim; Max := TabPAl^[PosMax];*)
  (*Min := 0.000119;*)
  (*i:= 0;*)
  (*WHILE TabPAl^[i] < 0.000119 DO i := i+1; END;*)
  (*PosMin := i;*)
  (*Max := 0.000240;*)
  (*i := 0;*)
  (*WHILE TabPAl^[i] < 0.000240 DO i := i+1; END;*)
  (*PosMax := i;*)

  (* Ecart entre les intervalles *)
  Ecart := (Max - Min) / IToLR(NbInter);
  (* Creation Tableau des intervalles *)
  CreateTab(TabEcart, LR, NbInter);
  (* Tableau du nombre elements par intervalle *)
  CreateTab(TabQtte, LI, NbInter);

  (* Initialisation du tableau des ecarts *)
  FOR j:= 0 TO NbInter-1 DO
    TabEcart^[j] := (Ecart*IToLR(j+1)) + Min;
    TabQtte^[j] := 0;
  END;

  (* Calcul du nombre d'elements pour chaque intervalle *)
  PosEcart:=0;
 (*FOR i:= PosMin TO PosMax DO
    WHILE (TabPAl^[i] > TabEcart^[PosEcart]) AND (PosEcart <= NbInter-1) DO
      PosEcart:= PosEcart + 1;
    END; 
    IF TabPAl^[i] <= TabEcart^[PosEcart] THEN    
      TabQtte^[PosEcart] := TabQtte^[PosEcart] + 1;
    ELSIF PosEcart = NbInter THEN    
      WHILE i<= PosMax DO      
        TabQtte^[PosEcart-1] := TabQtte^[PosEcart-1] + 1;
        i := i + 1;
      END;
    END;  
  END;*)
  
  (* Ecriture des resultats dans le fichier de sortie *)
  OpenAsOutput("Tab.dat");
  WriteLongReal(Min,5,5);
  WriteString("   ");     
  WriteInt(0,3);
  WriteLn;  
  FOR i:= 0 TO NbInter-1 DO
    WriteLongReal(TabEcart^[i],5,5);
    WriteString("   ");     
    WriteInt(TabQtte^[i],3);
    WriteLn;
  END;
  WriteLongReal(Max+Ecart,5,5);
  WriteString("   ");     
  WriteInt(0,3);
  WriteLn;
  DeleteTab(TabQtte, LI, NbInter);
  DeleteTab(TabEcart, LR, NbInter);
END MakeInterv;


(**************************************************************************)
(* Procedure qui calcule le P_Alpha(2) de maniere non efficace *)
PROCEDURE CalculPAlphaTest(Gen: CaractGenerateur; S: INTEGER ): LONGREAL;

VAR 
  Mult : LONGREAL;  
  Add : LONGREAL;
  i, j : INTEGER;
  Uij : LONGREAL;
  Modulo : LONGREAL;
  PtrTabUij : TabLR;
  PosTab : INTEGER;
  M, A, Seed, C : LONGINT; 
  Reste, Test : LONGREAL;

BEGIN
  (* Initialisation *)
  Mult := 1.0; 
  Add := 0.0; 
  M := IToLI(Gen.M);
  A := IToLI(Gen.A);
  Seed := IToLI(Gen.Seed);
  C := 0;
  Reste := 1.0;
  Modulo := REALToLR(FLOAT(Gen.M)); 
  SetLCG(M, A, C, Seed);
  
 
  (* Declaration d'un tableau de grandeur s pour garder *)
  (* les Uij qui serviront dans le deuxieme FOR         *)
  CreateTab (PtrTabUij, LR, S-1);
 
  FOR j:= 0 TO S-1 DO
    Uij := (Strip(0)); 
    PtrTabUij^[j] := Uij; 
    Mult  :=  Mult * (1.0 + DeuxPi2 * (1.0/6.0 + Uij*(Uij-1.0)));
    Reste := Reste * (1.0 + DeuxPi2/6.0); 
  END;
  Add := Add + Mult;

  FOR i := 1 TO Gen.M - 2 DO
    PosTab := (i-1) MOD S;  
    Mult:= 1.0;  
    FOR j:= 0 TO S-1 DO
      IF j # PosTab THEN
        Mult  :=  Mult * (1.0 + DeuxPi2 * (1.0/6.0 + PtrTabUij^[j]*(PtrTabUij^[j]-1.0))); 
      END; 
    END; 
    Uij := (Strip(0)); 
   
    Mult := Mult *(1.0 + DeuxPi2 * (1.0/6.0 + Uij * (Uij-1.0)));
    PtrTabUij^[PosTab] := Uij;  
    Add := Add + Mult; 
  END;

  DeleteTab (PtrTabUij, LR, S-1);
  Add := ((Add + Reste)/Modulo) - 1.0;  
  RETURN Add;
END CalculPAlphaTest;

END PALPHA.

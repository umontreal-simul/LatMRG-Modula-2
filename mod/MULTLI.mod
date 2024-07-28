IMPLEMENTATION MODULE MULTLI;

(*****************************************************************************)
(*                                                                           *)
(*                           MULT.MOD (Version LI)                           *)
(*                                                                           *)
(*  Ce module donne des outils pour travailler avec des scalaires, vecteurs  *)
(*  et matrices pour representer des multiplicateurs pour des LCG. Aussi,    *)
(*  le module permet de connaitre si un LCG donne une periode maximale.      *)
(*  Cette partie du module est inspiree du module PERMAX de Francois Blouin. *)
(*                                                                           *)
(*  Programmeurs : Francois Paradis                                          *)
(*  ------------   Marco Jacques                                             *)
(*                                                                           *)
(*  Date         : 12 juillet 1990                                           *)
(*  ----                                                                     *)
(*****************************************************************************)

FROM Storage  IMPORT ALLOCATE;
FROM MYINOUT  IMPORT WriteString, WriteLn;
FROM NUM      IMPORT LIToLR, ReadLI, WriteLI,
                     Round, MaxLongReal, MaxLongInt, IntToStrBase;
FROM SUPINT   IMPORT SuperInteger, Create, Delete, Affect;
FROM SUPCONV  IMPORT IntToSup, SupToInt;
FROM SUPARITH IMPORT Equal, Quotient, Greater, Subtract, PowerSupInt, Smaller,
                     Even, Add, DivideSupInt, Positive, Multiply;
FROM SUPFACT  IMPORT Factors, Factorize;
FROM CONFIG   IMPORT MMaxDim, MDim;


CONST
   SqrtMaxLI  = 46341;                 (* = TRUNC ( SQRT ( MaxLongInt ) ) *)
   H          = 32768;                 (* = 2^15.                         *)
   MMaxDegre  = MMaxDim*2;             (* Degre maximal d'un polynome     *) 
   MaxFactors = 200;

TYPE
   MDegre      = [0..MMaxDegre];
   InfoMPoly   = RECORD                (* Information about a polynomial  *)
      Degre    : MDegre;               (* polynomial degree               *)
      Coeff    : ARRAY MDegre OF MScal (* polynomial coefficients         *)
      END;
   MPoly       = POINTER TO InfoMPoly;
   NbFact      = [0..MaxFactors+1];
   IndFact     = [1..MaxFactors+1];
   VectFact    = ARRAY IndFact OF LONGINT;
   VectSupFact = ARRAY IndFact OF SuperInteger;

VAR
   M      : LONGINT;                   (* Modulo.                         *)
   ExpT1,                              (* Exposants de MPowerPolyMod et   *)
   ExpT2,                              (* de PuissPolyMod                 *)
   ExpT3,                              (* Exposants de SupPuissPolyMod    *)
   ExpT4,
   Sup1,                               (* =  1 en SuperEntier             *)
   SupMaxInt     : SuperInteger;       (* = MaxInt en SuperEntier         *)
   FactmMS1      : VectFact;           (* facteurs de m-1 (LI)            *)
   nFactmMS1     : NbFact;             (* nombre de facteurs de m-1       *)
   SupFactmMS1   : VectSupFact;        (* facteurs de m-1 (SI)            *)
   Factr         : VectFact;           (* facteurs de r <= MaxInt         *)
   nFactr        : NbFact;             (* nbre de facteurs de r <= MaxInt *)
   FactVerifr    : ARRAY IndFact OF BOOLEAN;
                                       (* =TRUE si le facteur a ete teste *)
   nVerifr       : INTEGER;            (* nbre de facteurs (<= MaxInt )   *)
                                       (* restant a verifier              *)
   IndP2         : IndFact;            (* Position dans Factr pour les    *)
                                       (* puiss de 2 ((Sup)PolyPuissMod)  *)
   SupFactr      : VectSupFact;        (* Facteurs premiers de r>MaxInt   *)
   nSupFactr     : NbFact;             (* Nombre de facteurs (> MaxInt)   *)
   SupFactVerifr : ARRAY IndFact OF BOOLEAN;
                                       (* =TRUE si le facteur a ete teste *)
   nSupVerifr    : INTEGER;            (* Nombre de facteurs (> MaxInt)   *)
                                       (* qui reste a tester              *)
   IndP2Sup      : IndFact;            (* Postion dans SupFactr pour les  *)
                                       (* puiss. de 2 ((Sup)PuissPolyMod) *)
   TestEchoue    : BOOLEAN;            (* =TRUE si le test pour un crite- *)
                                       (* re a echoue, FALSE sinon        *)
   PolyT1,
   PolyT2,
   PolyT3,
   PolyT4,
   f             : MPoly;
   qh, rh        : LONGINT;
   Temp          : MScal;
   PetitM        : BOOLEAN;
   mMS1, r,
   SupT,SupT1,
   Exp,Exp0      : SuperInteger;
   Order         : MDim;
   MChange       : BOOLEAN;
   Supm          : SuperInteger;

PROCEDURE MCreateScal (VAR S : MScal);
   BEGIN  END MCreateScal;

PROCEDURE MDeleteScal (VAR S : MScal);
   BEGIN  END MDeleteScal;
   
PROCEDURE MCreateVect (VAR V : MVect; k1, k2 : MDim);
   BEGIN  END MCreateVect;

PROCEDURE MDeleteVect (VAR V : MVect; k1, k2 : MDim);
   BEGIN  END MDeleteVect;


PROCEDURE MCreateMatr (VAR M : MMatr; k1, k2 : MDim);
   BEGIN  END MCreateMatr;
   
PROCEDURE MDeleteMatr (VAR M : MMatr; k1, k2 : MDim);
   BEGIN  END MDeleteMatr;

PROCEDURE MCreatePoly (VAR P : MPoly);
   BEGIN
   NEW (P);
   WITH P^ DO
      Coeff[0] := 0;
      Degre := 0;
      END
   END MCreatePoly;


PROCEDURE MReadScal (VAR S : MScal);
   BEGIN  ReadLI (S)  END MReadScal;


PROCEDURE MWriteScal (S : MScal);
   BEGIN  WriteLI (S, 16)  END MWriteScal;


PROCEDURE MWriteScalBin (S : MScal);
   (* Modifie par Yanick Champoux (2/98): la fct SignedToStr n'existe plus. *)
   VAR
      Str : ARRAY [0..32] OF CHAR;
   BEGIN
   IntToStrBase (S, 2, Str);
   WriteString (Str);   
   END MWriteScalBin;


PROCEDURE MWriteVect (VAR V : MVect;  n : MDim);
VAR
   j: MDim;
   BEGIN
   WriteLn;
   FOR j := 1 TO n DO
      MWriteScal ( V [j] )
      END
   END MWriteVect;


PROCEDURE MScalToLI (S : MScal) : LONGINT;
   BEGIN  RETURN S END MScalToLI;


PROCEDURE MScalToLR (S : MScal) : LONGREAL;
   BEGIN  RETURN LIToLR ( S )  END MScalToLR;


PROCEDURE MScalToSup
   ( S : MScal;
     T : SuperInteger
     );
   BEGIN IntToSup(S,T) END MScalToSup;


PROCEDURE SupToMScal (T : SuperInteger;  VAR  S : MScal);
   BEGIN SupToInt (T, S) END SupToMScal;

PROCEDURE LIToMScal ( I : LONGINT; VAR S : MScal );
   BEGIN  S := I  END LIToMScal;


PROCEDURE MAffect (S : MScal;  VAR T : MScal);
   BEGIN  T := S  END MAffect;


PROCEDURE MEqual (S, T : MScal): BOOLEAN;
   BEGIN  RETURN  (S = T) END MEqual;

PROCEDURE MGreater (S1, S2 : MScal): BOOLEAN;
   BEGIN RETURN  (S1 > S2) END MGreater;

PROCEDURE MSmaller (S1, S2 : MScal): BOOLEAN;
   BEGIN RETURN  (S1 < S2) END MSmaller;

PROCEDURE MChangeSign (VAR S : MScal);
   BEGIN S := -S  END MChangeSign;

PROCEDURE MInc (VAR S : MScal;   I : LONGINT);
   BEGIN S := S + I  END MInc;

PROCEDURE MAdd (S1, S2 : MScal;   VAR T : MScal);
   BEGIN T := S1 + S2  END MAdd;

PROCEDURE MSubtract (S1, S2 : MScal;   VAR T : MScal);
   BEGIN T := S1 - S2  END MSubtract;

PROCEDURE MAffectIdentMatr (VAR M : MMatr;  n : MDim);
VAR
   i, j: MDim;
   BEGIN
   FOR i := 1 TO n DO
      FOR j := 1 TO n DO
         IF i=j THEN M [i,j] := 1; ELSE M [i,j] := 0  END
         END
      END
   END MAffectIdentMatr;


PROCEDURE MCopyVect (VAR U, V : MVect;  n : MDim);
VAR
   j: MDim;
   BEGIN
   FOR j := 1 TO n  DO  V [j] := U [j]  END
   END MCopyVect;


PROCEDURE MCopyMatr (VAR M, N : MMatr; n : MDim);
VAR
  i, j: MDim; 
  BEGIN
   FOR i := 1 TO n DO
      FOR j := 1 TO n DO N[i,j] := M[i,j]  END
      END
   END MCopyMatr;


PROCEDURE MModifVect
   (VAR U,V : MVect;
          R : MScal;
          n : MDim);
   (* On effectue U = (U + RV) mod u  *)
   VAR
      i : MDim;
   BEGIN
   FOR i := 1 TO n DO U[i] := U[i] + R*V[i] END
   END MModifVect;


PROCEDURE MMultiply (T, S : MScal;   VAR R : MScal);
   BEGIN  R := T * S  END MMultiply;

PROCEDURE MQuotient (T, S : MScal;   VAR Q : MScal);
   BEGIN  Q := T DIV S  END MQuotient;

PROCEDURE MModulo (T, S : MScal;   VAR R : MScal);
   BEGIN  R := T MOD S  END MModulo;


PROCEDURE MSetm (m : MScal);
   BEGIN
   qh := m DIV H;   rh := m - H * qh;   M := m;
   PetitM := (m <= SqrtMaxLI);
   MChange := TRUE;
   END MSetm;

PROCEDURE MGetm (VAR m : MScal);
   BEGIN  m := M  END MGetm;


PROCEDURE MPowerLI (S : MScal;  i : LONGINT;  VAR R : MScal);
   VAR
      k : LONGINT;
   BEGIN
   R := 1;
   FOR k := 1 TO i DO  R := R * S   END;
   END MPowerLI;


PROCEDURE MProdModm (S, T : MScal;  VAR R : MScal);
   (* Retourne (S*T) MOD m.  Suppose que -m < S < m, -m < T < m.          *)
   (* (Voir L'Ecuyer et Cote (1987)).                                     *)
   VAR
      S0, S1, q, k : LONGINT;
   BEGIN
   IF S < 0 THEN INC (S, M) END;   IF T < 0 THEN INC (T, M) END;
   IF PetitM THEN  R := (S * T) MOD M;  RETURN  END;
   IF S < H THEN
      S0 := S;   R := 0
   ELSE
      S1 := S DIV H;   S0 := S - H * S1;
      IF S1 >= H THEN
         DEC ( S1, H );   k := T DIV qh;
         R := H * (T - k * qh) - k * rh;
         WHILE R < 0 DO INC (R, M) END
      ELSE  R := 0  END;
      IF S1 <> 0 THEN
         q := M DIV S1;   k := T DIV q;
         DEC (R, k * (M - S1 * q) );   IF R > 0 THEN DEC (R, M)  END;
         INC (R, S1 * (T - k * q) );   WHILE R < 0 DO INC (R, M)  END
         END;
      k := R DIV qh;   R := H * (R - k * qh) - k * rh;
      WHILE R < 0 DO INC (R, M)  END
      END;
   IF S0 <> 0 THEN
      q := M DIV S0;   k := T DIV q;
      DEC (R, k * (M - S0 * q) );   IF R > 0 THEN DEC (R, M)  END;
      INC (R, S0 * (T - k * q) );   WHILE R < 0 DO INC (R, M)  END
      END
   END MProdModm;


PROCEDURE MProdScalModm
 (VAR U, V : MVect;  VAR a, R : MScal;   n : MDim);
   (* soit U*V=aM+R;  calcule R = U*V modulo M                             *)
   (*                 et a = Round ( (RLR - R)/M )                         *)
   (*                      ou RLR = U*V (en LONGREAL)                      *)
   VAR
      P   : LONGINT;
      RLR : LONGREAL;
      j   : MDim;
   BEGIN
   R := 0;  RLR := 0.0;
   FOR j := 1 TO n DO
      RLR := RLR + LIToLR(U[j])*LIToLR(V[j]);
      MProdModm (U [j], V [j], P);
      IF P > 0 THEN
         IF R > (MaxLongInt - P) THEN
            DEC (R, M);
            INC (R, P)
         ELSE
            INC (R, P);
            IF R >= M THEN  DEC (R, M)  END
            END
      ELSE
         INC (R, P);
         IF R >= M THEN  DEC (R, M)  END
         END
      END;
   a := Round ((RLR - LIToLR(R)) / LIToLR(M))
   END MProdScalModm;

PROCEDURE MPowerModm (S, b : MScal;  VAR R : MScal);
   (* Retourne S^b MOD m dans R.  suppose -m < S < m,  b > 0.             *)
   VAR
      c : LONGINT;
   BEGIN
   IF S < 0 THEN INC (S, M)  END;
   IF b = 1 THEN  R := S;  RETURN  END;
   c := 1;
   REPEAT
      IF ODD (b) THEN  MProdModm (S, c, c)  END;
      MProdModm (S, S, S);   b := b DIV 2
   UNTIL b <= 1;
   MProdModm (S, c, R);
   END MPowerModm;

PROCEDURE MModifVectModm
    (VAR U,V : MVect;
           R : MScal;
           n : MDim);
    (* On effectue U = (U + RV) mod u  *)
    VAR
       i : MDim;
    BEGIN
    FOR i := 1 TO n DO U[i] := (U[i] + R*V[i]) MOD M END
    END MModifVectModm;

PROCEDURE MProdVectMatr
   (VAR V : MVect;  VAR N : MMatr;  VAR R : MVect;  n : MDim);
   VAR
      P : LONGINT;
      i, j: MDim;
   BEGIN
   FOR i := 1 TO n DO
      R [i] := 0;
      FOR j := 1 TO n DO
         MProdModm ( V [j], N [j,i], P);
         INC (R[i], P);
         IF R [i] >= M  THEN  DEC (R[i], M)  END
         END;
      END
   END MProdVectMatr;

PROCEDURE MSetf (VAR V : MVect; n : MDim);
   (* initialise f(x) = x^k - V[1]*x^(k-1) - ... - V[k] *)
   VAR
      i : MDegre;
   BEGIN
   WITH f^ DO
      Degre := n;
      FOR i := 1 TO n DO Coeff[n-i] := (-V[i]) MOD M END;
      Coeff[n] := 1;
      END
   END MSetf;


PROCEDURE PolyMod ( v  : MPoly );        (* Polynome dividende.             *)
   (* Calcule  v mod f (mod m), ou v et f sont des polynomes, et place le
      resultat dans  v. La procedure utilise l'algorithme de pseudo-
      division de polynomes, tel que decrit dans [Knuth2], p.407.          *)
   VAR
      i, j : CARDINAL;
   BEGIN
   WITH v^ DO
      IF Degre >= f^.Degre THEN
         (* Degre de v(x) >= Degre de f(x). *)
         FOR i := Degre - f^.Degre TO 0 BY -1 DO
            FOR j := f^.Degre + i - 1 TO i BY -1 DO
               MProdModm(Coeff [f^.Degre+i] , f^.Coeff [j-i] , Temp);
               DEC ( Coeff [j], Temp);
               IF Coeff [j] < 0 THEN
                 INC ( Coeff [j], M )  END;
               (* Lorsque j < i, on a v^.Coeff [j]*)
               (* = (f^.Coeff [f^.Degre] *        *)
               (* v^.Coeff [j]).                  *)
               END
            END;
         Degre := f^.Degre - 1;   (* Trouver le degre du polynome.   *)
         WHILE Coeff [Degre] = 0 DO
            DEC ( Degre )
            END
         END
      END
   END PolyMod;

(***************************************************************************)


PROCEDURE PolyCarreMod ( v : MPoly );   (* Le polynome a elever au carre.  *)
   (* Calcule  v^2 mod f (mod m)  et retourne le resultat dans  v  (v  est *)
   (* un polynome). La technique utilisee est tres conventionnelle, il     *)
   (* suffit de multiplier chaque coefficient du polynome par chacun des   *)
   (* autres coefficients.                                                 *)
   VAR
      i, j, s,
      DDegre  : CARDINAL;
      C       : LONGINT;
   BEGIN
   WITH v^ DO
      DDegre := 2 * Degre;
      FOR i := DDegre TO 0 BY -1 DO
         C := 0;
         IF i <= Degre THEN s := i ELSE s := Degre  END;
         FOR j := s TO (i - s) BY -1 DO
                                    (* Multiplier chaque coeff avec  *)
                                    (* les autres coeff.             *)
            MProdModm( Coeff [j] , Coeff [i-j] , Temp);
            C := (C - M) + Temp;
            IF C < 0 THEN INC ( C, M )  END
            END;
         Coeff [i] := C
         END;
      Degre := DDegre;                    (* Ajuster le degre du polynome  *)
                                          (* resultant.                    *)
      END;
   PolyMod ( v );
   END PolyCarreMod;


(***************************************************************************)


PROCEDURE MProdPolyMod ( u, v, w : MPoly);
   (* Calcule  u * v mod f (mod m), et place le resultat dans  w  (u,  v  *)
   (* et  w  sont des polynomes).                                         *)
   VAR
      i, j, d, f,
      SDegre     : CARDINAL;
      C          : LONGINT;
      t          : MPoly;       (* Pointeur temporaire.    *)
   BEGIN
   IF v^.Degre > u^.Degre THEN
      t := u;  u := v;  v := t  END;
   (* u  est le polynome de degre le plus eleve. *)

   WITH u^ DO
      SDegre := Degre + v^.Degre;
      FOR i := SDegre TO 0 BY -1 DO
         C := 0;
         IF i <= Degre THEN d := i ELSE d := Degre  END;
         IF d > v^.Degre THEN f := i - v^.Degre ELSE f := i - d  END;
         FOR j := d TO f BY -1 DO
            (* Multiplier chaque coeff. avec les autres coeff. *)
            MProdModm ( Coeff [j], v^.Coeff [i-j], Temp );
            C := (C - M) + Temp;
            IF C < 0 THEN INC ( C, M )  END
            END;
         w^.Coeff [i] := C
         END;

         w^.Degre := SDegre;       (* Ajuster le degre du polynome  *)
                                   (* resultant.                    *)
      END;
   PolyMod ( w );
   END MProdPolyMod;



PROCEDURE MPowerPolyMod
   ( VAR A : MVect;
         n : MDim;              (* Degre du polynome dividende. *)
         q : MScal;                   
     VAR R : MVect
     );

   (* Calcule  x^q mod f (mod m)  par mises au carre successives (voir *)
   (* [Knuth2] section 4.6.2 page 428).                                *)

   VAR
      ExpT1,                          (* ExpT1 est une puissance de 2. *)
      ExpT2    : LONGINT;
      i        : MDim;

   BEGIN
   IF  q = 0  THEN
      R[0] := 1;
      FOR  i := 1  TO  n-1  DO
         R[i] := 0
         END;
      RETURN
      END;
   MSetf (A,n);
   WITH PolyT1^ DO
      Degre := 1;
      Coeff [0] := 0; Coeff [1] := 1;
      END;
   (* PolyT1 = x *)
   ExpT1 := 1;

   WITH PolyT2^ DO
      Degre := 0;
      Coeff [0] := 1;
      END;
   (* PolyT2 = 1 *)
   ExpT2 := 0;

   WHILE ( q > 1 ) DO
      IF ODD ( q ) THEN
         MProdPolyMod ( PolyT1, PolyT2, PolyT2 );
         INC ( ExpT2, ExpT1 );
         (* PolyT2 = x^ExpT2 mod f (mod m). *)
         END;
                                          (* Verifie que si  r / ExpT2 est *)
                                          (* facteur premier de  r, alors  *)
                                          (* le degre de PolyT2 est > 0.   *)
      PolyCarreMod ( PolyT1 );
      INC ( ExpT1, ExpT1 );
      (* PolyT1 = x^ExpT1 mod f (mod m),  ExpT1 est une puissance de 2. *)
      q := q DIV 2
      END;
   MProdPolyMod ( PolyT1, PolyT2, PolyT1 );

   FOR i := 0 TO f^.Degre-1 DO R[i] := PolyT1^.Coeff[i] END
   END MPowerPolyMod;


(***************************************************************************)


PROCEDURE Trier ( VAR L : Factors );

   (* Trie les facteurs de la liste de L en ordre DECROISSANT. *)

   VAR
      T,
      PrecF, CurF,
      PrecPG, CurPG,
      PrecH, CurH, NextH : Factors;

   BEGIN
   (* L # NIL. *)
   PrecH := NIL; CurH := L; NextH := CurH^.Next;
   WHILE NextH # NIL DO
      (* Trouver le plus grand a partir de CurH^. *)
      PrecF := CurH; CurF := NextH;
      PrecPG := PrecH; CurPG := CurH;
      WHILE CurF # NIL DO
         IF Greater ( CurF^.Factor, CurPG^.Factor ) THEN
            PrecPG := PrecF; CurPG := CurF
            END;
         PrecF := CurF; CurF := CurF^.Next
         END;
      (* CurPG^ est le plus grand facteur trouve (a partir de CurH^). *)
      IF CurH # CurPG THEN
         (* Interchanger le facteur courant CurH et *)
         (* le plus grand trouve CurPG.             *)
         IF PrecH # NIL THEN
            PrecH^.Next := CurPG
         ELSE
            L := CurPG
            END;
         T := CurPG^.Next;
         IF CurPG # NextH THEN
            CurPG^.Next := NextH;
            PrecPG^.Next := CurH
         ELSE
            CurPG^.Next := CurH
            END;
         CurH^.Next := T
         END;
      PrecH := CurPG; CurH := PrecH^.Next; NextH := CurH^.Next
      END
   END Trier;

(***************************************************************************)


PROCEDURE VerifProdFact ( L : Factors; n : SuperInteger ) : BOOLEAN;
   (* Verifie si le produit des facteurs de la liste L est bien egal a n. *)
   VAR
      Verif : BOOLEAN;
      P, PF : SuperInteger;
   BEGIN
   Create ( P, 2 ); Create ( PF, 2 );
   IntToSup ( 1, PF );
   WHILE L # NIL DO
      PowerSupInt ( L^.Factor, L^.Multiplicity, P );
      Multiply ( PF, P, PF );
      L := L^.Next
      END;
   IF Equal ( n, PF ) THEN
      Verif := TRUE
   ELSE
      Verif := FALSE
      END;
   Delete ( P ); Delete ( PF );
   RETURN Verif
   END VerifProdFact;


PROCEDURE IdentFactmMS1 ( VAR ListFact : Factors );
   (* Identifie les facteurs (m-1)/q, pour tout q facteur premier de (m-1). *)
   VAR
      i : IndFact;
      L : Factors;
   BEGIN
   IF ListFact <> NIL THEN
      IF NOT VerifProdFact ( ListFact, mMS1 ) THEN
         WriteString
            ( '** ERREUR PerMax ** Produit des facteurs lus <> de (m-1).' );
         WriteLn;
         HALT
         END;
      L := ListFact
   ELSE
      (* Decomposer (m-1) en facteurs premiers. *)
      Factorize ( mMS1, MaxLongReal, L );
      END;

   (* Placer les facteurs (m-1)/q en ordre croissant dans les structures de *)
   (* donnees appropriees.                                                  *)
   Trier ( L );    (* en ordre decroissant. *)
   ListFact := L;
   i := 1; nFactmMS1 := 0;
   WHILE L # NIL DO
      Create ( SupFactmMS1 [i], 2 );
      SupToInt ( L^.Factor, FactmMS1 [i] );
      FactmMS1 [i] := (M - 1) DIV FactmMS1 [i];
      IntToSup ( FactmMS1 [i], SupFactmMS1 [i] );
      INC ( i ); INC ( nFactmMS1 );
      L := L^.Next
      END;
   END IdentFactmMS1;


(***************************************************************************)


PROCEDURE IdentFactr ( VAR ListFact : Factors );
   (* Identifie les facteurs r/q, pour tout q facteur premier de r. *)
   VAR
      L : Factors;
   BEGIN
   IF ListFact <> NIL THEN
      IF NOT VerifProdFact ( ListFact, r ) THEN
         WriteString ( '** ERREUR PerMax ** Produit des facteurs lus <> r.' );
         WriteLn;
         HALT
         END;
      L := ListFact
   ELSE
      Factorize ( r, MaxLongReal, L );
      END;

   (* Placer les facteurs r/q en ordre croissant dans les structures de *)
   (* donnees appropriees.                                              *)
   Trier ( L ); (* en ordre decroissant. *)
   ListFact := L;
   nFactr := 0; nSupFactr := 0;
   IF Equal ( L^.Factor, r ) THEN RETURN  END;
   REPEAT
      Quotient ( r, L^.Factor, SupT );
      IF Greater ( SupT, SupMaxInt ) THEN
         INC ( nSupFactr );
         Create ( SupFactr [nSupFactr], 2 );
         Affect ( SupT, SupFactr [nSupFactr] )
      ELSE
         INC ( nFactr );
         SupToInt ( SupT, Factr [nFactr] )
         END;
      L := L^.Next
   UNTIL L = NIL;
   END IdentFactr;


(***************************************************************************)


PROCEDURE SetFactors
   ( VAR ListmMS1,
         Listr : Factors;
         k     : MDim
     );
   (* Si ListmMS1 = NIL, alors on calcule les facteurs de (m-1) et on *)
   (* retourne la liste triee dans ListmMS1; sinon on verifie si la   *)
   (* liste de facteurs donne bien mMS1 et si non, on imprime un mes- *)
   (* sage d'erreur, et on s'arrete. Idem pour Listr (facteurs de r)  *)
   (* Aussi, si on remarque que m et Order n'ont pas ete change, alors*)
   (* on ne effectue aucun calcul                                     *)

   BEGIN
   IF NOT MChange AND (k = Order) THEN RETURN END;
   Order := k;
   IntToSup (M, Supm);
   Create ( mMS1, 2 );
   IntToSup ( M-1, mMS1 );               (* mMS1 = m - 1.                 *)
   IdentFactmMS1 (ListmMS1);
   Delete ( mMS1 );
   PowerSupInt ( Supm, VAL (LONGCARD, Order), r );
   Subtract ( r, Sup1, r );              (* r = m**Ordre - 1.             *)
   Subtract ( Supm, Sup1, SupT);         (* SupT = m - 1.                 *)
   Quotient ( r, SupT, r );              (* r = (m**Ordre - 1) / (m - 1). *)
   (* Pour PeriodeMaximale. *)
   IdentFactr (Listr);
   MChange := FALSE
   END SetFactors;


PROCEDURE PrimElem (VAR A : MVect) : BOOLEAN;
   (* Verifie si  (-1)^(Ordre+1) * A [Ordre]  est element primitif modulo  m *)
   (* avec ( ABS (A [Ordre]) < m ).                                          *)
   VAR
      i    : IndFact;
      t    : LONGINT;
      temp : MScal;
   BEGIN
   IF A [Order] = 0 THEN RETURN FALSE  END;
   IF ODD ( Order ) THEN
      t := A [Order]
   ELSE
      t := - A [Order]
      END;
   (* IF t < 0 THEN INC ( t, m )  END; *)
   (* t = (-1)^(Ordre+1) * A [Ordre] mod m. PuissModm accepte des *)
   (* arguments positifs ou negatifs.                             *)
   i := 1;
   WHILE i <= nFactmMS1 DO
      MPowerModm (t, FactmMS1[i], temp);
      IF temp = 1 THEN  RETURN FALSE   END;
      INC (i)
      END;
   RETURN TRUE
   END PrimElem;


(***************************************************************************)
(* ajmal - 15 Nov 1996 *)
PROCEDURE Initialisations(VAR A : MVect);   (* + ajmal 15 Nov 1996 *)
   VAR
      i : INTEGER;
   BEGIN
   TestEchoue := FALSE;
   nVerifr := nFactr;
   IndP2 := 1;
   nSupVerifr := nSupFactr;
   IndP2Sup := 1;
   FOR i := 1 TO VAL (INTEGER, nFactr) DO  FactVerifr [i] := FALSE  END;
   FOR i := 1 TO VAL (INTEGER, nSupFactr) DO SupFactVerifr [i] := FALSE END;
   MSetf (A, Order);
   END Initialisations;

PROCEDURE Valide
   ( Polynome : MPoly;                    (* = x^k mod f(x) mod m.         *)
     k        : LONGINT;                  (* Exposant a verifier (< 2^31). *)
     VAR i    : IndFact                   (* Position dans Factr.          *)
   ) : BOOLEAN;

   (* Verifie que si  k  est dans Factr (r/k  est facteur premier de  r),  *)
   (* alors le degre de  Polynome=x^k mod f (mod m)  est > 0 (critere iii).*)
   (* k est representable sur un LONGINT. La recherche dans Factr commence *)
   (* a la position i.                                                     *)

   BEGIN
   IF nVerifr > 0 THEN
      (* Verifier si  k  est facteur de  r. Les facteurs sont en ordre  *)
      (* croissant.                                                     *)
      WHILE ( i <= nFactr ) AND (( Factr [i] < k )
				   OR FactVerifr [i] ) DO
	 INC ( i )
	 END;
      IF i <= nFactr THEN
	 IF Factr [i] = k THEN
	    (* k  divise  r  et il n'a pas ete verifie. *)
	    IF Polynome^.Degre > 0 THEN
	       DEC ( nVerifr );
	       FactVerifr [i] := TRUE
	    ELSE
	       TestEchoue := TRUE
	       END
	    END
	 END
      END;
   RETURN NOT (TestEchoue)
   END Valide;

PROCEDURE SupValide
   ( Polynome : MPoly;                    (* = x^k mod f(x) mod m.         *)
     k        : SuperInteger;             (* Exposant a verifier.          *)
     VAR i    : IndFact                   (* Position dans SupFactr.       *)
   )  : BOOLEAN;

   (* Verifie que si  k  est dans SupFactr (r/k est facteur premier de r), *)
   (* alors le degre de  Polynome^k mod f (mod m)  est > 0 (critere iii).  *)
   (* La recherche dans SupFactr commence a la position i.                 *)

   BEGIN
   IF nSupVerifr > 0 THEN
      WHILE ( i <= nSupFactr ) AND ( Smaller ( SupFactr [i], k )
				     OR SupFactVerifr [i] ) DO
	 INC ( i )  END;
      IF i <= nSupFactr THEN
	 IF Equal ( SupFactr [i], k ) THEN
	    (* k  divise  r  et il n'a pas ete verifie. *)
	    IF Polynome^.Degre > 0 THEN
	       DEC ( nSupVerifr );
	       SupFactVerifr [i]  := TRUE
	    ELSE
	       TestEchoue := TRUE
	       END
	    END
	 END
      END;
   RETURN NOT (TestEchoue)
   END SupValide;

PROCEDURE PolyPuissMod
   ( q : LONGINT                           (* Degre du polynome dividende. *)
   )  : MPoly;

   (* Calcule  x^q mod f (mod m)  par mises au carre successives (voir *)
   (* [Knuth2] section 4.6.2 page 428).                                *)
   (* q > 0.                                                           *)

   VAR
      ExpT1,                              (* ExpT1 est une puissance de 2. *)
      ExpT2    : LONGINT;
      IndExpT2 : IndFact;

   BEGIN
   WITH PolyT1^ DO
      Degre := 1;
      Coeff [0] := 0; Coeff [1] := 1;
      END;
   (* PolyT1 = x *)
   ExpT1 := 1;

   WITH PolyT2^ DO
      Degre := 0;
      Coeff [0] := 1;
      END;
   (* PolyT2 = 1 *)
   ExpT2 := 0;   IndExpT2 := 1;

   WHILE ( q > 1 ) DO
      IF ODD ( q ) THEN
	 MProdPolyMod ( PolyT1, PolyT2, PolyT2 );
	 INC ( ExpT2, ExpT1 );
	 (* PolyT2 = x^ExpT2 mod f (mod m). *)
	 IF NOT Valide ( PolyT2, ExpT2, IndExpT2 ) THEN
	    RETURN NIL                    (* Pour sortir au plus vite.     *)
	    END
	 END;
					  (* Verifie que si  r / ExpT2 est *)
					  (* facteur premier de  r, alors  *)
					  (* le degre de PolyT2 est > 0.   *)
      PolyCarreMod ( PolyT1 );
      INC ( ExpT1, ExpT1 );
      (* PolyT1 = x^ExpT1 mod f (mod m),  ExpT1 est une puissance de 2. *)
      IF Valide ( PolyT1, ExpT1, IndP2 ) THEN
	 q := q DIV 2
      ELSE
	 RETURN NIL                       (* Pour sortir au plus vite.     *)
	 END
      END;
   MProdPolyMod ( PolyT1, PolyT2, PolyT1 );

   RETURN PolyT1;

   END PolyPuissMod;

PROCEDURE SupPolyPuissMod
   ( q              : SuperInteger;       (* Degre du polynome dividende.  *)
     VAR PolyResult : MPoly               (* + ajmal 15 Nov 1996           *)
   )  : MPoly;

   (* Fait la meme chose que PolyPuissMod pour  q > MaxInt.  Appelle *)
   (* PolyPuissMod des que  q - puissance calculee =< MaxInt.        *)
   VAR
      i         : LONGINT;
      IndExp,
      IndExpT4  : IndFact;
      SupExpT3,                               (* = TRUE si ExpT3 > MaxInt. *)
      SupExpT4  : BOOLEAN;                    (* = TRUE si ExpT4 > MaxInt. *)

   BEGIN
   IF NOT Greater ( q, SupMaxInt ) THEN
      SupToInt ( q, i );
      RETURN PolyPuissMod ( i )
      END;

   (* q > MaxInt. *)
   Affect ( q, Exp );
   WITH PolyT3^ DO
      Degre := 1;
      Coeff [0] := 0; Coeff [1] := 1;
      END;
   (* PolyT3 = x *)
   IntToSup ( 1, ExpT3 ); SupExpT3 := FALSE;

   WITH PolyT4^ DO
      Degre := 0;
      Coeff [0] := 1;
      END;
   (* PolyT4 = 1 *)
   IntToSup ( 0, ExpT4 ); IndExpT4 := 1; SupExpT4 := FALSE;
   Subtract ( Exp, ExpT3, Exp0 );

   WHILE Greater ( Exp0, SupMaxInt ) AND NOT TestEchoue DO
      IF NOT Even ( Exp ) THEN
	 MProdPolyMod ( PolyT4, PolyT3, PolyT4 );
	 Subtract ( Exp0, ExpT3, Exp0 );
	 Add ( ExpT4, ExpT3, ExpT4 );
	 (* PolyT4 = x^ExpT4 mod f (mod m). *)
	 IF SupExpT4 THEN
	    IF NOT SupValide ( PolyT4, ExpT4, IndExpT4 ) THEN
	       RETURN NIL  END
	 ELSE
	    IF Greater ( ExpT4, SupMaxInt ) THEN
	       SupExpT4 := TRUE;
	       IndExpT4 := 1;
	       IF NOT SupValide ( PolyT4, ExpT4, IndExpT4 ) THEN
		  RETURN NIL  END
	    ELSE
	       SupToInt ( ExpT4, i );
	       IF NOT Valide ( PolyT4, i, IndExpT4 ) THEN
		  RETURN NIL  END
	       END
	    END
	 END;

      IF Greater ( Exp0, SupMaxInt ) THEN
					  (* Verifie que si  r / ExpT4 est *)
					  (* facteur premier de  r, alors  *)
					  (* le degre de PolyT4 est > 0.   *)
	 PolyCarreMod ( PolyT3 );         (* ou PolyProdMod ??    *)
	 Subtract ( Exp0, ExpT3, Exp0 );
	 Add ( ExpT3, ExpT3, ExpT3 );
	 (* PolyT3 = x^ExpT3 mod f mod m, ExpT3 est une puissance de 2. *)
	 IF SupExpT3 THEN
	    IF NOT SupValide ( PolyT3, ExpT3, IndP2Sup ) THEN
	       RETURN NIL  END
	 ELSE
	    IF Greater ( ExpT3, SupMaxInt ) THEN
	       SupExpT3 := TRUE;
	       IndP2 := nFactr + 1;
	       (* IndP2Sup = 1. *)
	       IF NOT SupValide ( PolyT3, ExpT3, IndP2Sup ) THEN
		  RETURN NIL  END
	    ELSE
	       SupToInt ( ExpT3, i );
	       IF NOT Valide ( PolyT3, i, IndP2 ) THEN
		  RETURN NIL  END
	       END
	    END;
	 DivideSupInt ( Exp, 2, Exp, i )
	 END
      END;

   MProdPolyMod ( PolyT3, PolyT4, PolyT3 );
   Add ( ExpT3, ExpT4, ExpT3 );
   (* PolyT3 = x^ExpT3 mod f (mod m). *)
   IndExp := IndP2Sup;
   IF SupValide ( PolyT3, ExpT3, IndExp ) THEN
      IF Positive ( Exp0 ) THEN
	 (* Exp0 > 0 *)
	 SupToInt ( Exp0, i );
	 PolyResult := PolyPuissMod ( i );
	 (* PolyResult = x^i mod f (mod m). *)
	 IndExp := 1;
	 IF Valide ( PolyResult, i, IndExp ) THEN
	    MProdPolyMod ( PolyT3, PolyResult, PolyT3 )
	    END
	 END
      END;
   RETURN PolyT3

   END SupPolyPuissMod;

PROCEDURE MaxPeriod (VAR  A : MVect) : BOOLEAN;
   (* Verifie les criteres (ii) et (iii) du test de periode maximale. La   *)
   (* fonction evalue d'abord  x^r mod f (mod m)  pour verifier le critere *)
   (* (ii). Les valeurs de  r/q, q  fact. premier de r, rencontrees lors   *)
   (* de cette evaluation sont testees selon le critere (iii). A la fin on *)
   (* applique le test du critere (iii) aux facteurs qui restent.          *)

   VAR
      i          : CARDINAL;
      C          : LONGINT;             (* Variable temporaire.            *)
      PolyResult : MPoly;               (* Pointe au polynome resultant de *)
                                        (* la serie de tests.              *)

(***************************************************************************)
(* deplacee a l'exterieur ajmal 15 Nov 1996
   PROCEDURE Initialisations;
      VAR
         i : INTEGER;
      BEGIN
      TestEchoue := FALSE;
      nVerifr := nFactr;
      IndP2 := 1;
      nSupVerifr := nSupFactr;
      IndP2Sup := 1;
      FOR i := 1 TO VAL (INTEGER, nFactr) DO  FactVerifr [i] := FALSE  END;
      FOR i := 1 TO VAL (INTEGER, nSupFactr) DO SupFactVerifr [i] := FALSE END;
      MSetf (A, Order);
      END Initialisations;
end ajmal *)

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* deplacee a l'exterieur ajmal 15 Nov 1996 
   PROCEDURE Valide
      ( Polynome : MPoly;
        k        : LONGINT;
        VAR i    : IndFact
      ) : BOOLEAN;

      BEGIN
      IF nVerifr > 0 THEN
         WHILE ( i <= nFactr ) AND (( Factr [i] < k )
                                      OR FactVerifr [i] ) DO
            INC ( i )
            END;
         IF i <= nFactr THEN
            IF Factr [i] = k THEN
               IF Polynome^.Degre > 0 THEN
                  DEC ( nVerifr );
                  FactVerifr [i] := TRUE
               ELSE
                  TestEchoue := TRUE
                  END
               END
            END
         END;
      RETURN NOT (TestEchoue)
      END Valide;
end ajmal *)

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* deplacee a l'exterieur ajmal 15 Nov 1996 
   PROCEDURE SupValide
      ( Polynome : MPoly;
        k        : SuperInteger;
        VAR i    : IndFact
      )  : BOOLEAN;

      BEGIN
      IF nSupVerifr > 0 THEN
         WHILE ( i <= nSupFactr ) AND ( Smaller ( SupFactr [i], k )
                                        OR SupFactVerifr [i] ) DO
            INC ( i )  END;
         IF i <= nSupFactr THEN
            IF Equal ( SupFactr [i], k ) THEN
               IF Polynome^.Degre > 0 THEN
                  DEC ( nSupVerifr );
                  SupFactVerifr [i]  := TRUE
               ELSE
                  TestEchoue := TRUE
                  END
               END
            END
         END;
      RETURN NOT (TestEchoue)
      END SupValide;
end ajmal *)

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* deplacee a l'exterieur ajmal 15 Nov 1996
   PROCEDURE PolyPuissMod
      ( q : LONGINT
      )  : MPoly;

      VAR
         ExpT1,
         ExpT2    : LONGINT;
         IndExpT2 : IndFact;

      BEGIN
      WITH PolyT1^ DO
         Degre := 1;
         Coeff [0] := 0; Coeff [1] := 1;
         END;
      ExpT1 := 1;

      WITH PolyT2^ DO
         Degre := 0;
         Coeff [0] := 1;
         END;
      ExpT2 := 0;   IndExpT2 := 1;

      WHILE ( q > 1 ) DO
         IF ODD ( q ) THEN
            MProdPolyMod ( PolyT1, PolyT2, PolyT2 );
            INC ( ExpT2, ExpT1 );
            IF NOT Valide ( PolyT2, ExpT2, IndExpT2 ) THEN
               RETURN NIL
               END
            END;
         PolyCarreMod ( PolyT1 );
         INC ( ExpT1, ExpT1 );
         IF Valide ( PolyT1, ExpT1, IndP2 ) THEN
            q := q DIV 2
         ELSE
            RETURN NIL
            END
         END;
      MProdPolyMod ( PolyT1, PolyT2, PolyT1 );

      RETURN PolyT1;

      END PolyPuissMod;
end ajmal *)

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* deplacee a l'exterieur ajmal 15 Nov 1996
   PROCEDURE SupPolyPuissMod
      ( q : SuperInteger
      )  : MPoly;

      VAR
         i         : LONGINT;
         IndExp,
         IndExpT4  : IndFact;
         SupExpT3,
         SupExpT4  : BOOLEAN;

      BEGIN
      IF NOT Greater ( q, SupMaxInt ) THEN
         SupToInt ( q, i );
         RETURN PolyPuissMod ( i )
         END;

      Affect ( q, Exp );
      WITH PolyT3^ DO
         Degre := 1;
         Coeff [0] := 0; Coeff [1] := 1;
         END;
      IntToSup ( 1, ExpT3 ); SupExpT3 := FALSE;

      WITH PolyT4^ DO
         Degre := 0;
         Coeff [0] := 1;
         END;
      IntToSup ( 0, ExpT4 ); IndExpT4 := 1; SupExpT4 := FALSE;
      Subtract ( Exp, ExpT3, Exp0 );

      WHILE Greater ( Exp0, SupMaxInt ) AND NOT TestEchoue DO
         IF NOT Even ( Exp ) THEN
            MProdPolyMod ( PolyT4, PolyT3, PolyT4 );
            Subtract ( Exp0, ExpT3, Exp0 );
            Add ( ExpT4, ExpT3, ExpT4 );
            IF SupExpT4 THEN
               IF NOT SupValide ( PolyT4, ExpT4, IndExpT4 ) THEN
                  RETURN NIL  END
            ELSE
               IF Greater ( ExpT4, SupMaxInt ) THEN
                  SupExpT4 := TRUE;
                  IndExpT4 := 1;
                  IF NOT SupValide ( PolyT4, ExpT4, IndExpT4 ) THEN
                     RETURN NIL  END
               ELSE
                  SupToInt ( ExpT4, i );
                  IF NOT Valide ( PolyT4, i, IndExpT4 ) THEN
                     RETURN NIL  END
                  END
               END
            END;
               
         IF Greater ( Exp0, SupMaxInt ) THEN
            PolyCarreMod ( PolyT3 );
            Subtract ( Exp0, ExpT3, Exp0 );
            Add ( ExpT3, ExpT3, ExpT3 );
            IF SupExpT3 THEN
               IF NOT SupValide ( PolyT3, ExpT3, IndP2Sup ) THEN
                  RETURN NIL  END
            ELSE
               IF Greater ( ExpT3, SupMaxInt ) THEN
                  SupExpT3 := TRUE;
                  IndP2 := nFactr + 1;
                  IF NOT SupValide ( PolyT3, ExpT3, IndP2Sup ) THEN
                     RETURN NIL  END
               ELSE
                  SupToInt ( ExpT3, i );
                  IF NOT Valide ( PolyT3, i, IndP2 ) THEN
                     RETURN NIL  END
                  END
               END;
            DivideSupInt ( Exp, 2, Exp, i )
            END
         END;

      MProdPolyMod ( PolyT3, PolyT4, PolyT3 );
      Add ( ExpT3, ExpT4, ExpT3 );
      IndExp := IndP2Sup;
      IF SupValide ( PolyT3, ExpT3, IndExp ) THEN
         IF Positive ( Exp0 ) THEN
            SupToInt ( Exp0, i );
            PolyResult := PolyPuissMod ( i );
            IndExp := 1;
            IF Valide ( PolyResult, i, IndExp ) THEN
               MProdPolyMod ( PolyT3, PolyResult, PolyT3 )
               END
            END
         END;
      RETURN PolyT3

      END SupPolyPuissMod;
end ajmal *)

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)


   BEGIN   (* PeriodeMaximale *)
   IF Order = 1 THEN RETURN TRUE  END;
   (* ajmal 15 Nov 1996 *)
   (* Initialisations;  *)
   Initialisations(A);

   (* ajmal 15 Nov 1996                    *)
   (* PolyResult := SupPolyPuissMod ( r ); *)
   PolyResult := SupPolyPuissMod ( r, PolyResult );
   (* PolyResult = x^r mod f (mod m)  si aucun test n'a encore echoue. *)

   IF TestEchoue THEN RETURN FALSE  END;

   (* Verifier critere (ii). *)
   IF ODD ( Order ) THEN C := A [Order] ELSE C := -A [Order] END;
   IF C < 0 THEN INC ( C, M )  END;
   (* C = (-1)^(Ordre+1) * A [Ordre] mod m *)
   IF (NOT (PolyResult^.Degre = 0)) OR
          (NOT (PolyResult^.Coeff [0] = C)) THEN
      RETURN FALSE;
      END;

   (* Tester les facteurs premiers =< MaxInt de  r  qui n'ont pas encore   *)
   (* ete testes selon le critere (iii) de Knuth.                          *)
   i := 1;
   WHILE nVerifr > 0 DO
      IF NOT FactVerifr [i] THEN
         PolyResult := PolyPuissMod ( Factr [i] );
         IF TestEchoue THEN RETURN FALSE  END;
         DEC ( nVerifr );
         IF PolyResult^.Degre = 0 THEN RETURN FALSE  END
         END;
      INC ( i )
      END;

   (* Tester les facteurs premiers > MaxInt de  r  qui n'ont pas encore    *)
   (* ete testes selon le critere (iii) de Knuth.                          *)
   i := 1;
   WHILE nSupVerifr > 0 DO
      IF NOT SupFactVerifr [i] THEN
         (* ajmal 15 Nov 1996                               *)
         (* PolyResult := SupPolyPuissMod ( SupFactr [i] ); *)
         PolyResult := SupPolyPuissMod ( SupFactr [i], PolyResult );
         IF TestEchoue THEN RETURN FALSE  END;
         DEC ( nSupVerifr );
         IF PolyResult^.Degre = 0 THEN RETURN FALSE  END
         END;
      INC ( i )
      END;
   RETURN TRUE;
   END MaxPeriod;


BEGIN
MZero := 0; MOne := 1;  MTwo := 2;
Create      (Supm, 1);
Create      (Sup1, 1);  IntToSup (1, Sup1);
MCreatePoly (PolyT1);   MCreatePoly (PolyT2);
MCreatePoly (PolyT3);   MCreatePoly (PolyT4);    MCreatePoly(f);
Create      (SupT,2);   Create      (SupT1,2);
Create      (ExpT1,2);  Create      (ExpT2,2);
Create      (ExpT3,2);  Create      (ExpT4,2);
Create      (Exp,2);    Create      (Exp0,2);    Create(ExpT3,2);
Create      (ExpT4,2);  Create      (SupMaxInt,1);
IntToSup    (2147483647, SupMaxInt);
Create      (r,2);
END MULTLI.

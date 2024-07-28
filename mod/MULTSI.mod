IMPLEMENTATION MODULE MULTSI;

(*****************************************************************************)
(*                                                                           *)
(*                           MULT.MOD (Version SI)                           *)
(*                                                                           *)
(*  Ce module donne des outils pour travailler avec des scalaires, vecteurs  *)
(*  et matrices pour representer des multiplicateurs pour des LCG. Aussi,    *)
(*  le module permet de connaitre si un LCG donne une periode maximale.      *)
(*  Cette partie du module est inspiree du module PERMAX de Francois Blouin. *)
(*                                                                           *)
(*  Programmeurs : Francois Paradis                                          *)
(*  ------------   Marco Jacques                                             *)
(*                 Josee Turgeon                                             *)
(*                 Pierre L'Ecuyer                                           *)
(*****************************************************************************)


FROM Storage  IMPORT ALLOCATE;
FROM MYINOUT  IMPORT WriteString, WriteLn, Write;
FROM SUPINT   IMPORT SuperInteger, Delete, Create, Affect, ReadSup, WriteSup;
FROM SUPCONV  IMPORT IntToSup, SupToInt, SupToLongReal;
FROM SUPARITH IMPORT ChangeSign, Negative, Smaller, Add, Subtract,
                     Equal, Quotient, MultMod, Multiply, Divide,
                     Zero, Even, PowerMod, Modulo, Greater, DivideSupInt,
                     Positive, PowerSupInt;
FROM SUPFACT  IMPORT Factors, Factorize;
FROM CONFIG   IMPORT MMaxDim, MDim;

CONST
   MSizeSI = 2;                        (* Used in MCreateScal             *)
   MMaxDegre  = 2*MMaxDim;             (* Degre maximum d'un polynome     *)
   MaxFactors = 200;                   (* Nombre max. de facteurs d'un    *)
                                       (* nombre                          *)
TYPE
   MDegre      = [0..MMaxDegre];
   InfoMPoly   = RECORD                (* Information about a polynom     *)
      Degre    : MDegre;               (* polynom degree                  *)
      Coeff    : ARRAY MDegre OF MScal (* polynom coefficients            *)
      END;
   MPoly       = POINTER TO InfoMPoly;
   NbFact      = [0..MaxFactors+1];
   IndFact     = [1..MaxFactors+1];
   VectFact    = ARRAY IndFact OF LONGINT;
   VectSupFact = ARRAY IndFact OF SuperInteger;


VAR
   M      : SuperInteger;              (* Modulo.                         *)
   TwoSI  : MScal;                     (* Deux en Super-Entier            *)
   ExpT1,                              (* Exposants de MPowerPolyMod et   *)
   ExpT2,                              (* de PuissPolyMod                 *)
   ExpT3,                              (* Exposants de SupPuissPolyMod    *)
   ExpT4,
   SupT,                               (* Variables temporaires           *)
   SupT1  : SuperInteger;
   PolyT1,                             (* Polynomes temporaires           *)
   PolyT2,
   PolyT3,
   PolyT4,
   f             : MPoly;              (* Polynome f(x)                   *)
   mMS1          : SuperInteger;       (* (m-1) en SuperEntier            *)
   SupFactmMS1   : VectSupFact;        (* Facteurs de (m-1) en S-Entiers  *)
   nFactmMS1     : NbFact;             (* Nombre de ces facteurs          *)
   Factr         : VectFact;           (* Facteurs premiers de r<=MaxInt  *)
   nFactr        : NbFact;             (* Nombre de facteurs de r<=MaxInt *)
   FactVerifr    : ARRAY IndFact OF BOOLEAN;
                                       (* =TRUE si le facteur a ete teste *)
   nVerifr       : INTEGER;            (* nombre de facteurs (<= MaxInt)  *)
                                       (* qui reste a verifier            *)
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
   Exp,                                (* Exposants temporaires           *)
   Exp0,
   r,                                  (* r = (m^k - 1) / (m - 1)         *)
   SupMaxInt     : SuperInteger;       (* = MaxInt en Super-Entier        *)
   MChange       : BOOLEAN;            (* Si la valeur de m a ete change  *)
   Order         : MDim;               (* l'ordre du generateur           *)


(****************************************************************************)

PROCEDURE MCreateScal (VAR S : MScal);
   (* Cree le scalaire S                                           *)
   BEGIN  Create (S, MSizeSI)  END MCreateScal;
   
PROCEDURE MDeleteScal (VAR S : MScal);
   BEGIN  Delete (S) END MDeleteScal;


PROCEDURE MCreateVect (VAR V : MVect; k1, k2 : MDim);
   VAR  
      i : MDim;
   BEGIN
   FOR  i := k1  TO  k2  DO  Create(V[i], MSizeSI)  END
   END MCreateVect;
   
PROCEDURE MDeleteVect (VAR V : MVect; k1, k2 : MDim);
   VAR  
      i : MDim;
   BEGIN
   FOR  i := k1  TO  k2  DO  Delete(V[i])  END
   END MDeleteVect;


PROCEDURE MCreateMatr (VAR M : MMatr; k1, k2 : MDim);
   VAR
      i : MDim;
   BEGIN
   IF  k1 <= k2  THEN
      IF  k1 > 0  THEN
         FOR  i := 0  TO  k1-1  DO
            MCreateVect(M[i], k1, k2)
            END
         END;
      FOR  i := k1  TO  k2  DO
         MCreateVect(M[i], 0, k2)
         END
      END
   END MCreateMatr;
   
PROCEDURE MDeleteMatr (VAR M : MMatr; k1, k2 : MDim);
   VAR
      i : MDim;
   BEGIN
   IF  k1 <= k2  THEN
      IF  k1 > 0  THEN
         FOR  i := 0  TO  k1-1  DO
            MDeleteVect(M[i], k1, k2)
            END
         END;
      FOR  i := k1  TO  k2  DO
         MDeleteVect(M[i], 0, k2)
         END
      END
   END MDeleteMatr;

PROCEDURE MCreatePoly (VAR P : MPoly);
   (* Cree le polynome P, ou les coefficients de P sont des MScal  *)
   VAR i : MDegre;
   BEGIN
   NEW (P);
   WITH P^ DO
      FOR i := 0 TO MMaxDegre DO  MCreateScal (Coeff[i]) END;
      IntToSup(0,Coeff[0]);
      Degre := 0;
      END
   END MCreatePoly;
   
PROCEDURE MEqual (S, T : MScal): BOOLEAN;
   BEGIN
   IF  Equal(S, T)  THEN  RETURN TRUE  ELSE  RETURN  FALSE  END
   END MEqual;

PROCEDURE MGreater (S1, S2 : MScal): BOOLEAN;
   BEGIN  
   IF  Greater(S1, S2)  THEN  RETURN TRUE  ELSE  RETURN FALSE  END  
   END MGreater;

PROCEDURE MSmaller (S1, S2 : MScal): BOOLEAN;
   BEGIN RETURN  Smaller(S1, S2) END MSmaller;

PROCEDURE MChangeSign (S : MScal);
   BEGIN
   ChangeSign (S, S)
   END MChangeSign;

PROCEDURE MInc (VAR S : MScal; I : LONGINT);
   BEGIN
   IntToSup (I, SupT);
   Add (S, SupT, S)
   END MInc;

PROCEDURE MAdd (S1, S2 : MScal;  VAR S3 : MScal);
   BEGIN
   Add (S1, S2, S3)
   END MAdd;

PROCEDURE MSubtract (S1, S2 : MScal;  VAR S3 : MScal);
   BEGIN
   Subtract (S1, S2, S3)
   END MSubtract;

PROCEDURE MReadScal (VAR S : MScal);
   (* Lit le scalaire S du fichier d'entree courant                *)
   BEGIN  ReadSup (S, 10)  END MReadScal;


PROCEDURE MWriteScal (S : MScal);
   (* Ecrit le scalaire S dans le fichier de sortie courant        *)
   BEGIN  WriteSup (S, 10, 80)  END MWriteScal;

PROCEDURE MWriteScalBin (S : MScal);
   BEGIN  WriteSup (S, 2, 80)  END MWriteScalBin;


PROCEDURE MWriteVect
   ( VAR V : MVect;
         n : MDim
   );
   VAR
      j : MDim;
   BEGIN
   WriteLn;
   FOR j := 1 TO n DO
      MWriteScal (V [j]);  IF j<n THEN Write ( CHR(9) ) END;
      END
   END MWriteVect;


PROCEDURE MScalToLI
   ( S : MScal
     ) : LONGINT;
   (* Convertit un MScal en LONGINT                                *)
   VAR R : LONGINT;
   BEGIN
   SupToInt ( S, R );
   RETURN ( R )
   END MScalToLI;


PROCEDURE MScalToLR
   ( S : MScal
     ) : LONGREAL;
   (* Convertit un MScal en LONGREAL                               *)
   VAR R : LONGREAL;
   BEGIN
   SupToLongReal ( S, R );
   RETURN ( R )
   END MScalToLR;


PROCEDURE MScalToSup
   ( S : MScal;
     T : SuperInteger
     );
   (* Convertit un MScal en SuperInteger                           *)
   BEGIN
   Affect(S,T)
   END MScalToSup;


PROCEDURE LIToMScal
   (     I : LONGINT;
     VAR S : MScal
     );
   (* Convertit un LONGINT en MScal                                *)
   BEGIN  IntToSup ( I, S )  END LIToMScal;


PROCEDURE MAffect
   (     S : MScal;
     VAR T : MScal
     );
   (* Affect a T, la valeur de S                                   *)
   BEGIN  Affect (S, T)  END MAffect;


PROCEDURE MAffectIdentMatr
   ( VAR M : MMatr;
         n : MDim
     );
   VAR
      i, j : MDim;
   BEGIN
   FOR i := 1 TO n DO
      FOR j := 1 TO n DO
         IF i=j THEN IntToSup(1, M [i,j]) ELSE IntToSup(0, M [i,j])  END
         END
      END
   END MAffectIdentMatr;


PROCEDURE MCopyVect
   ( VAR U, V : MVect;
            n : MDim
     );
   VAR
      j : MDim;
   BEGIN
   FOR j := 1 TO n DO  Affect (U [j], V [j])  END
   END MCopyVect;


PROCEDURE MCopyMatr
   ( VAR M, N : MMatr;
            n : MDim
     );
   VAR
      i, j : MDim;
   BEGIN
   FOR i := 1 TO n DO
      FOR j := 1 TO n DO Affect(M[i,j], N[i,j])  END
      END
   END MCopyMatr;

PROCEDURE MModifVect
   ( VAR U,V : MVect;
           R : MScal;
           n : MDim
     );
   (* Ajoute a U, R fois le vecteur V                             *)
   VAR
      i : MDim;
   BEGIN
   FOR i := 1 TO n DO
      Multiply(R,V[i],U[0]);
      Add(U[i],U[0],U[i]);
      END
   END MModifVect;

PROCEDURE MPowerLI
   (     S : MScal;
         i : LONGINT;
     VAR R : MScal
     );
   (* Effectue S^I et retourne le resultat dans R                  *)
   VAR
      k : LONGINT;
   BEGIN
   IntToSup (1, R);
   FOR k := 1 TO i DO  Multiply (S, R, R)  END
   END MPowerLI;


PROCEDURE MMultiply (T, S : MScal;   VAR  R : MScal);
   BEGIN  Multiply (T, S, R) END MMultiply;

PROCEDURE MQuotient (T, S : MScal;   VAR  Q : MScal);
   BEGIN  Quotient (T, S, Q) END MQuotient;

PROCEDURE MModulo (T, S : MScal;   VAR  R : MScal);
   BEGIN  Modulo (T, S, R) END MModulo;


PROCEDURE MSetm (m : MScal);
   (* Affecte la valeur de M. Les procedures dessous utiilsent M   *)
   BEGIN  Affect (m, M);   MChange := TRUE  END MSetm;


PROCEDURE MGetm (VAR m : MScal);
   BEGIN  Affect (M, m)  END MGetm;


PROCEDURE MModm (S : MScal; VAR R : MScal);
   BEGIN
   Divide (S, M, SupT, R)
   END MModm;


PROCEDURE MProdModm (S, T : MScal;   VAR R : MScal);
   BEGIN  MultMod (S, T, M, R)  END MProdModm;


PROCEDURE MProdScalModm
   ( VAR U, V : MVect;
     VAR Q, R : MScal;
            n : MDim
     );
   VAR
      j : MDim;
   BEGIN
   IntToSup (0, R);
   FOR j := 1 TO n DO
      Multiply (U[j], V[j], V[0]);
      Add (R, V[0], R)
      END;
   Divide (R, M, Q, R)
   END MProdScalModm;

PROCEDURE MPowerModm (S, b : MScal;   VAR R : MScal);
   BEGIN  PowerMod (S, b, M, R)  END MPowerModm;


PROCEDURE MModifVectModm
    (VAR U,V : MVect;
           R : MScal;
           n : MDim);
    (* On effectue U = (U + RV) mod u  *)
    VAR
       i : MDim;
    BEGIN
    FOR i := 1 TO n DO
       Multiply (R, V[i], U[0]);   Add (U[i], U[0], U[i]);
       Modulo (U[i], M, U[i])
       END
    END MModifVectModm;


PROCEDURE MSetf (VAR V : MVect;   n : MDim);
   VAR
      i : MDegre;
   BEGIN
   WITH f^ DO
      Degre := n;
      FOR i := 1 TO n DO Subtract(M,V[i],Coeff[n-i]) END;
      LIToMScal(1, Coeff[n])
      END
   END MSetf;


PROCEDURE PolyMod (v : MPoly);          (* Polynome dividende.             *)
   (* Calcule  v mod f (mod m), ou v et f sont des polynomes, et place le  *)
   (* resultat dans  v. La procedure utilise l'algorithme de pseudo-       *)
   (* division de polynomes, tel que decrit dans [Knuth2], p.407.          *)
   VAR
      i, j : CARDINAL;
   BEGIN
   WITH v^ DO
      IF Degre >= f^.Degre THEN
      (* Degre de v(x) >= Degre de f(x). *)
         FOR i := Degre - f^.Degre TO 0 BY -1 DO
            FOR j := f^.Degre + i - 1 TO i BY -1 DO
               MultMod ( Coeff [f^.Degre+i], f^.Coeff [j-i],
                         M, SupT );
               Subtract ( Coeff [j], SupT, Coeff [j] );
               IF Negative ( Coeff [j] ) THEN
                  Add ( Coeff [j], M, Coeff [j] )
                  END;
               (* Lorsque j < i, on a v^.Coeff [j]*)
               (* = (f^.Coeff [f^.Degre] *        *)
               (* v^.Coeff [j]).                  *)
               END
            END;
         Degre := f^.Degre - 1;   (* Trouver le degre du polynome.   *)
         WHILE Zero ( Coeff [Degre] ) DO DEC ( Degre ) END
         END;
      FOR i := f^.Degre TO 2*f^.Degre DO MAffect(MZero,Coeff[i]) END;
      END
   END PolyMod;


PROCEDURE PolyCarreMod( v : MPoly );    (* Le polynome a elever au carre.  *)
   (* Calcule  v^2 mod f (mod m)  et retourne le resultat dans  v  (v  est *)
   (* un polynome). La technique utilisee est tres conventionnelle, il     *)
   (* suffit de multiplier chaque coefficient du polynome par chacun des   *)
   (* autres coefficients.                                                 *)

   VAR
      i, j, s,
      DDegre  : MDegre;
   BEGIN
   WITH v^ DO
      DDegre := 2 * Degre;
      FOR i := DDegre TO 0 BY -1 DO
         IntToSup ( 0, SupT );
         IF i <= Degre THEN s := i ELSE s := Degre  END;
         FOR j := s TO (i - s) BY -1 DO
            (* Multiplier chaque coeff avec les autres coeff. *)
            MultMod ( Coeff [j], Coeff [i-j], M, SupT1 );
            Add ( SupT, SupT1, SupT );
            IF NOT Smaller ( SupT, M ) THEN
               Subtract ( SupT, M, SupT );
               END
            (* SupT = SupT + SupCoeff [j] * SupCoeff [i-j] mod m. *)
            END;
         Affect ( SupT, Coeff [i] )
         END;
      Degre := DDegre;                    (* Ajuster le degre du polynome  *)
                                          (* resultant.                    *)
      END;
   PolyMod ( v );
   END PolyCarreMod;


PROCEDURE MProdPolyMod( u, v, w : MPoly);
   (* Calcule  u * v mod f (mod m), et place le resultat dans  w  (u,  v  *)
   (* et  w  sont des polynomes).                                         *)
   VAR
   i, j, d, f,
   SDegre     : MDegre;
   t          : MPoly;       (* Pointeur temporaire.    *)
   BEGIN
   IF v^.Degre > u^.Degre THEN
      t := u;  u := v;  v := t  END;
   (* u  est le polynome de degre le plus eleve. *)
   WITH u^ DO
      SDegre := Degre + v^.Degre;
      FOR i := SDegre TO 0 BY -1 DO
         IntToSup ( 0, SupT );
         IF i <= Degre THEN d := i ELSE d := Degre  END;
         IF d > v^.Degre THEN f := i - v^.Degre ELSE f := i - d  END;
         FOR j := d TO f BY -1 DO
            (* Multiplier chaque coeff. avec les autres coeff. *)
            MultMod ( Coeff [j], v^.Coeff [i-j], M, SupT1 );
            Add ( SupT, SupT1, SupT );
            IF NOT Smaller ( SupT, M ) THEN
               Subtract ( SupT, M, SupT );
               END
            (* SupT= SupT + u^.SupCoeff[j] * v^.SupCoeff[i-j] mod m. *)
            END;
            Affect ( SupT, w^.Coeff [i] )
         END
      END;
   w^.Degre := SDegre;       (* Ajuster le degre du polynome  *)
                             (* resultant.                    *)
   PolyMod ( w );
   END MProdPolyMod;


PROCEDURE MPowerPolyMod
   ( VAR A  : MVect;
         n  : MDim;                       (* Degre du polynome dividende. *)
         q  : MScal;                   
     VAR R  : MVect);

   VAR
      i : MDim;
   (* Calcule  x^q mod f (mod m)  par mises au carre successives (voir *)
   (* [Knuth2] section 4.6.2 page 428).                                *)
   BEGIN
   IF  Zero(q)  THEN
      IntToSup(1, R[0]);
      FOR  i := 1  TO  n-1  DO
         IntToSup(0, R[i])
         END;
      RETURN
      END;
   MSetf(A,n);
   WITH PolyT1^ DO
      Degre := 1;
      IntToSup ( 0, Coeff [0] );
      IntToSup ( 1, Coeff [1] );
      END;
   (* PolyT1 = x *)
   IntToSup(1,ExpT1);

   WITH PolyT2^ DO
      Degre := 0;
      IntToSup ( 1, Coeff [0] );
      END;
   (* PolyT2 = 1 *)
   IntToSup(0,ExpT2);

   WHILE Greater( q ,MOne ) DO
      IF NOT Even ( q ) THEN
         MProdPolyMod ( PolyT1, PolyT2, PolyT2 );
         Add ( ExpT2, ExpT1 ,ExpT2);
         (* PolyT2 = x^ExpT2 mod f (mod m). *)
         END;
      PolyCarreMod ( PolyT1 );
      Add ( ExpT1, ExpT1 ,ExpT1);
      (* PolyT1 = x^ExpT1 mod f (mod m),  ExpT1 est une puissance de 2. *)
      Quotient(q,TwoSI,q);
      END;

   MProdPolyMod ( PolyT1, PolyT2, PolyT1 );
   FOR i := 0 TO f^.Degre-1 DO MAffect (PolyT1^.Coeff[i],R[i]) END
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


(***************************************************************************)


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
      Factorize ( mMS1, 60.0, L );
      END;

   (* Placer les facteurs (m-1)/q en ordre croissant dans les structures de *)
   (* donnees appropriees.                                                  *)
   Trier ( L );    (* en ordre decroissant. *)
   ListFact := L;
   i := 1; nFactmMS1 := 0;
   WHILE L # NIL DO
      Create ( SupFactmMS1 [i], 2 );
      Quotient ( mMS1, L^.Factor, SupFactmMS1 [i] );
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
      Factorize ( r, 60.0, L );
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
   Create ( mMS1, 2 );
   Subtract ( M, MOne, mMS1 );           (* mMS1 = m - 1.                 *)
   IdentFactmMS1 (ListmMS1);
   Delete ( mMS1 );
   PowerSupInt ( M, Order, r );
   Subtract ( r, MOne, r );              (* r = m**Ordre - 1.             *)
   Subtract ( M, MOne, SupT);            (* SupT = m - 1.                 *)
   Quotient ( r, SupT, r );              (* r = (m**Ordre - 1) / (m - 1). *)
   (* Pour PeriodeMaximale. *)
   IdentFactr (Listr);
   MChange := FALSE
   END SetFactors;

(***************************************************************************)

PROCEDURE PrimElem
   ( VAR A : MVect
   ) : BOOLEAN;
   (* Verifie si  (-1)^(Order+1) * A [Order]  est element primitif modulo  m *)
   (* avec ( ABS (A [Order]) < m ).                                          *)
   VAR
      i : IndFact;
   BEGIN  (* Element Primitif *)
   IF Zero ( A [Order] ) THEN RETURN FALSE  END;
   IF ODD ( Order ) THEN
      Affect ( A [Order], SupT )
   ELSE
      ChangeSign ( A [Order], SupT )
      END;
   (* SupT = (-1)^(Order+1) * A [Order]. PowerMod accepte des arguments *)
   (* positifs ou negatifs.                                             *)
   i := 1;
   WHILE i <= nFactmMS1 DO
      PowerMod ( SupT, SupFactmMS1 [i], M, SupT1 );
      IF Equal ( SupT1, MOne ) THEN
         RETURN FALSE
         END;
      INC ( i )
      END;
   RETURN TRUE
   END PrimElem;

(***************************************************************************)
(* ajmal - 15 Nov 1996 *)
PROCEDURE Initialisations(VAR A : MVect);   (* + ajmal 15 Nov 1996 *)
   VAR
      i : NbFact;
   BEGIN
   TestEchoue := FALSE;
   nVerifr := nFactr;
   IndP2 := 1;
   nSupVerifr := nSupFactr;
   IndP2Sup := 1;
   FOR i := 1 TO nFactr DO
      FactVerifr [i] := FALSE END;
   FOR i := 1 TO nSupFactr DO
      SupFactVerifr [i] := FALSE END;

   (* Initialisation du polynome f(x). *)
   MSetf(A,Order);
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
      IntToSup ( 0, Coeff [0] );
      IntToSup ( 1, Coeff [1] );
      END;
   (* PolyT1 = x *)
   ExpT1 := 1;

   WITH PolyT2^ DO
      Degre := 0;
      IntToSup ( 1, Coeff [0] );
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
      IntToSup ( 0, Coeff [0] );
      IntToSup ( 1, Coeff [1] );
      END;
   (* PolyT3 = x *)
   IntToSup ( 1, ExpT3 ); SupExpT3 := FALSE;

   WITH PolyT4^ DO
      Degre := 0;
      IntToSup ( 1, Coeff [0] );
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


PROCEDURE MaxPeriod
   ( VAR A : MVect
   ) : BOOLEAN;
   (* Verifie les criteres (ii) et (iii) du test de periode maximale. La   *)
   (* fonction evalue d'abord  x^r mod f (mod m)  pour verifier le critere *)
   (* (ii). Les valeurs de  r/q, q  fact. premier de r, rencontrees lors   *)
   (* de cette evaluation sont testees selon le critere (iii). A la fin on *)
   (* applique le test du critere (iii) aux facteurs qui restent.          *)
   VAR
      i          : CARDINAL;
      PolyResult : MPoly;               (* Pointe au polynome resultant de *)
                                        (* la serie de tests.              *)


   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* deplacee a l'exterieur ajmal 15 Nov 1996 
   PROCEDURE Initialisations;
      VAR
         i : NbFact;
      BEGIN
      TestEchoue := FALSE;
      nVerifr := nFactr;
      IndP2 := 1;
      nSupVerifr := nSupFactr;
      IndP2Sup := 1;
      FOR i := 1 TO nFactr DO
         FactVerifr [i] := FALSE END;
      FOR i := 1 TO nSupFactr DO
         SupFactVerifr [i] := FALSE END;

      (* Initialisation du polynome f(x). *)
      MSetf(A,Order);
      END Initialisations;
end ajmal *)

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

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

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

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

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

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
         IntToSup ( 0, Coeff [0] );
         IntToSup ( 1, Coeff [1] );
         END;
      ExpT1 := 1;

      WITH PolyT2^ DO
         Degre := 0;
         IntToSup ( 1, Coeff [0] );
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

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

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
         IntToSup ( 0, Coeff [0] );
         IntToSup ( 1, Coeff [1] );
         END;
      IntToSup ( 1, ExpT3 ); SupExpT3 := FALSE;

      WITH PolyT4^ DO
         Degre := 0;
         IntToSup ( 1, Coeff [0] );
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

   (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

   BEGIN   (* PeriodeMaximale *)
   IF Order = 1 THEN RETURN TRUE  END;
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
   (* m > MaxInt. *)
   IF ODD ( Order ) THEN
      Affect ( A [Order], SupT )
   ELSE
      ChangeSign ( A [Order], SupT )
      END;
   IF Negative ( SupT ) THEN Add ( M, SupT, SupT )  END;
   (* SupT = (-1)^(Ordre+1) * A [Ordre] mod m *)
   IF (NOT (PolyResult^.Degre = 0)) OR
           (NOT Equal (PolyResult^.Coeff [0], SupT)) THEN
      RETURN FALSE
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
      INC (i)
      END;
   RETURN TRUE;
   END MaxPeriod;

(****************************************************************************)
(* initialization part *)

BEGIN
MCreateScal (M);
MCreateScal (TwoSI);    IntToSup (2, TwoSI);
MCreateScal (MOne);     MCreateScal (MZero);     MCreateScal (MTwo);
LIToMScal   (1, MOne);  LIToMScal   (0, MZero);  LIToMScal   (2, MTwo);
MCreatePoly (PolyT1);   MCreatePoly (PolyT2);
MCreatePoly (PolyT3);   MCreatePoly (PolyT4);    MCreatePoly (f);
Create (SupT, 2);   Create (SupT1, 2);
Create (ExpT1, 2);  Create (ExpT2, 2);
Create (Exp, 2);    Create (Exp0, 2);    Create (ExpT3, 2);
Create (ExpT4, 2);  Create (SupMaxInt, 1);   Create (r, 2);
IntToSup (2147483647, SupMaxInt);
MChange := TRUE;
END MULTSI.

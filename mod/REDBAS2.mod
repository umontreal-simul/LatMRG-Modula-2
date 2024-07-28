IMPLEMENTATION MODULE REDBAS2;


FROM SYSTEM   IMPORT ADDRESS;
FROM Storage  IMPORT ALLOCATE;
FROM NUM      IMPORT hLR, chLR, Sqrt, Trunc, IToLR, LIToLR, S; 
FROM MYINOUT  IMPORT WriteInt, WriteString, WriteLn;

FROM SUPINT   IMPORT SuperInteger, Create;
FROM SUPARITH IMPORT Equal, Smaller, DivideLR;
FROM SUPCONV  IMPORT IntToSup;

IMPORT BASISLR;
FROM LATBASIS IMPORT Basis, InitBasis, CreateBasis, CopyBasis, Permute;
FROM REDBAS   IMPORT ReductMinkowski, ShortestVector, TransformStage3;
FROM CONFIG   IMPORT BMaxDim, BDim;
FROM MULT     IMPORT MScal;
FROM NORM     IMPORT NormType;
FROM CONVERT  IMPORT SupToMScal;
FROM BASIS    IMPORT BVect, BCreateVect, BAffect, BProdScalSI, BConvLR, BZero,
                     BModifVectLR, BChangeSignVect, BModifVectLI, BCopyVect;

TYPE
   BasisList  = POINTER TO InfoBasis;
   InfoBasis  = RECORD
      base : Basis;
      di   : BDim;
      NextBasis : BasisList
      END;

VAR
   l             : BDim;
   h, h2, h3, H, i1h : BASISLR.BVect;
   BZeroVect     : BVect;
   S1, S2, S4    : SuperInteger;
   B1            : Basis;
   basislist, currentbasis, lastbasis  : BasisList;
   lengthbasislist : LONGINT;
   curmaxdim        : BDim;

(* Inutile?
PROCEDURE BConvVectLR (VAR vLR : BASISLR.BVect; v : BVect; d : BDim);
   VAR
      i : BDim;
   BEGIN
   FOR  i := 1  TO  d  DO
      vLR[i] := BConvLR(v[i])
      END
   END BConvVectLR;
*)

PROCEDURE GCDvect (VAR z : BASISLR.BVect;  k, n : BDim) : LONGREAL;
   (* Calcule le plus grand commun diviseur de z[k],...,z[n].               *)
   VAR i : BDim;
       c, d, r : LONGINT;
       zLI : ARRAY BDim OF LONGINT;
   BEGIN
   FOR  i := k  TO  n  DO
      zLI[i] := Trunc(z[i])
      END;
   d := ABS(zLI[k]);
   i := k+1;
   WHILE (d#1) AND (i<=n) DO
      c := ABS(zLI[i]);
      WHILE c#0 DO
         r := d MOD c;  d := c;  c := r;
         END;  (* d = GCD (d, z[i]). *)
      INC (i);
      END;
   RETURN LIToLR(d)
   END GCDvect;

PROCEDURE CalculErr
   (B : Basis;
    VAR DC2, LDC2 : BASISLR.BVect;
    VAR C0, EC0 : BASISLR.BMatr;
    d : BDim);

   (* LIMITATION PROVISOIRE: lorsque les BScal sont des SuperInteger,       *)
   (* les vecteurs de la base B doivent pouvoir etre representes exactement *)
   (* en LONGREAL.                                                          *)

   VAR
      i, j, k : BDim;
      C2, EC2, VLR, WLR : BASISLR.BMatr; (*  Matrice de Choleski de degre 2. *)
      m2, e, e1, e2, terme, x : BASISLR.BScal;

   BEGIN

   WITH  B^  DO
      m2 := mLR*mLR;
      (*  Conversion en LONGREAL.  *)
      FOR  i := 1  TO  Dim  DO
         FOR  k := 1  TO  Dim  DO
            VLR[i,k] := BConvLR (V[i,k]);
            WLR[i,k] := BConvLR (W[i,k])
            END
         END;

      FOR  i := 1  TO  d  DO
         FOR  j := i  TO  Dim  DO
            (*  Calcul de C2[i,j] et de l'erreur numerique due a ce calcul. *)
            C2[i,j] := 0.0;
            e1 := 0.0;
            FOR  k := 1  TO  Dim  DO
               terme := VLR[i,k]*VLR[j,k];
               C2[i,j] := C2[i,j] + terme;
               e1 := e1 + ABS (terme)
               END;
            e1 := S (h3[Dim]*e1);
            x := 0.0;
            e2 := 0.0;
            FOR  k := 1  TO  i-1  DO
               terme := C0[k,i]*C2[k,j];
               x := x + terme;
               e2 := e2 + ABS (terme)
               END;
            e2 := S (h3[i-1]*e2);
            C2[i,j] := C2[i,j] - x;
            e := S (S (hLR*ABS (C2[i,j])) + S (e1 + e2));

            (*  Calcul d'un majorant de l'erreur sur C2[i,j].  *)
            EC2[i,j] := e;
            FOR  k := 1  TO  i-1  DO
               EC2[i,j] := S (EC2[i,j]
                  + S (S (EC0[k,i]*ABS (C2[k,j]))
                      + S (S (ABS (C0[k,i]) + EC0[k,i])*EC2[k,j])))
               END;

            IF  i = j  THEN
               DC2[i] := C2[i,i];
               LDC2[i] := chLR*(DC2[i] - EC2[i,i])
            ELSE
               (*  Calcul de C0[i,j].  *)
               C0[i,j] := C2[i,j]/DC2[i];

               (*  Calcul d'un majorant de l'erreur sur C0[i,j].  *)
               EC0[i,j] := S (S (EC2[i,j]
                   + S (ABS (C0[i,j])*EC2[i,i] + S (hLR*S (ABS (C0[i,j])))*C2[i,j]))
                               /LDC2[i])
               END
            END
         END;

      FOR  i := Dim  TO  d+1  BY  -1  DO
         (*  Calcul de la i-ieme ligne de la matrice de Choleski            *)
         (*  duale de degre 2, et calcul d'erreur.                          *)
         FOR  j := i  TO  1  BY  -1  DO
            C2[i,j] := 0.0;
            e1 := 0.0;
            FOR  k := 1  TO  Dim  DO
               terme := WLR[i,k]*WLR[j,k];
               C2[i,j] := C2[i,j] + terme;
               e1 := e1 + ABS (terme)
               END;
            e1 := S (h3[Dim]*e1);
            x := 0.0;
            e2 := 0.0;
            FOR  k := i+1  TO  Dim  DO
               terme := C0[k,i]*C2[k,j];
               x := x + terme;
               e2 := e2 + ABS (terme)
               END;
            e2 := S (h3[Dim-i]*e2);
            C2[i,j] := C2[i,j] - x;
            e := S (S (hLR*ABS (C2[i,j])) + S (e1 + e2));
            EC2[i,j] := e;
            FOR  k := i + 1  TO  Dim  DO
               EC2[i,j] := S (EC2[i,j]
                  + S (S (EC0[k,i]*ABS (C2[k,j]))
                        + S (S (ABS (C0[k,i]) + EC0[k,i])*EC2[k,j])))
               END;

            IF  i # j  THEN
               C0[i,j] := C2[i,j]/C2[i,i];
               EC0[i,j] := S (S (EC2[i,j]
                  + S (ABS (C0[i,j])*EC2[i,i] + S (hLR*S (ABS (C0[i,j])))*C2[i,j]))
                               /(chLR*(C2[i,i] - EC2[i,i])))
               END
            END;

         (*  Calcul de l'entree diagonale sur la i-ieme ligne de la matrice *)
         (*  de Choleski de degre 2 et calcul d'erreur.                     *)
         DC2[i] := m2/C2[i,i];
         EC2[i,i] := S (S (hLR*S (m2/chLR) + S (S (hLR*S (DC2[i]/chLR)*C2[i,i])
                      + S (DC2[i]*EC2[i,i])))/(chLR*(C2[i,i] - EC2[i,i])));
         LDC2[i] := chLR*(DC2[i] - EC2[i,i]);

         (*  Calcul de la i-ieme ligne de la matrice de Choleski            *)
         (*  de degre 0, et calcul d'erreur.                                *)
         FOR  j := i+1  TO  Dim  DO
            C0[i,j] := -C0[j,i];
            e := 0.0;
            FOR  k := i+1  TO  j-1  DO
               terme := C0[k,i]*C0[k,j];
               C0[i,j] := C0[i,j] - terme;
               e := e + ABS (terme)
               END;
            e := S (h3[j-i]*e);
            EC0[i,j] := e;
            FOR  k := i+1  TO  j-1  DO
               EC0[i,j] := S (EC0[i,j]
                   + S (S (EC0[k,i]*ABS (C0[k,j]))
                        + S (S (ABS (C0[k,i]) + EC0[k,i])*EC0[k,j])))
               END;
            EC0[i,j] := S (EC0[i,j] + EC0[j,i])
            END
         END
      END
   END CalculErr;

(*-------------------------------------------------------------------------*)
(* ajmal 15 Nov 1996 *)

PROCEDURE VerifZ 
   ( B                         : Basis;
     j                         : BDim;
     VAR E, E1, e, x, mdc      : LONGREAL;
     VAR C0, EC0               : BASISLR.BMatr;
     VAR zLR, R2, LDC2, zshort : BASISLR.BVect;
     VAR Stage                 : INTEGER;
     VAR idem                  : BOOLEAN;
     VAR i                     : BDim;
     VAR zLI                   : BASISLR.VectLI;
     VAR d                     : BDim ) : BOOLEAN;

(* Retourne TRUE lorsqu'on ne trouve pas de vecteur plus court.         *)
   VAR
      min, max  : LONGINT;
      center    : LONGREAL;
      zcurrent  : LONGINT;
      k, h      : BDim;
      tempm     : MScal;
   BEGIN
   WITH  B^  DO
      (* Calcul d'un intervalle contenant les valeurs admissibles de    *)
      (* zj.Il pourrait eventuellement en contenir qui ne le sont pas.  *)
      center := 0.0;
      IF  j < Dim  THEN
	 (* Calcul approximatif du centre de l'intervalle ainsi que     *)
	 (* d'un majorant de la valeur absolue de l'erreur commise.     *)
	 E := 0.0;
	 E1 := 0.0;
	 FOR  k := j+1  TO  Dim  DO
	    e := C0[j,k]*zLR[k];
	    center := center + e;
	    E1 := E1 + ABS(e);
	    (* Majorant de l'erreur sur chaque terme.                   *)
	    e := S(S(EC0[j,k]*ABS(zLR[k])) + hLR*S(ABS(e)));
	    E := E + e
	    END;
	 center := -center;
	 k := Dim - j;
	 E := S(S(h2[k]*E) + S(H[k]*E1));

	 IF  j = 1  THEN
	    x := center - E;
	    IF  x > 0.0  THEN
	       min := Trunc(chLR*x);
	    ELSE
	       min := Trunc(S(x)); DEC(min)
	       END;
	    x := center + E;
	    IF  x > 0.0  THEN
	       max := Trunc(S(x)); INC(max)
	    ELSE
	       max := Trunc(chLR*x)
	       END
	 ELSE

	    (* Majorant de la distance du centre approximatif aux       *)
	    (* extremites de l'intervalle.                              *)
	    mdc := S(S(Sqrt(S(R2[j]/LDC2[j]))) + E);

	    (* Calcul de deux entiers ayant la propriete qu'un entier   *)
	    (* non-compris entre (i.e. strictement exterieur `a)        *)
	    (* ceux-ci n'appartient pas a l'intervalle.                 *)
	    x := center - mdc;
	    IF  x > 0.0  THEN
	       min := Trunc(chLR*x); INC(min)
	    ELSE
	       min := Trunc(S(x))
	       END;
	    x := center + mdc;
	    IF  x > 0.0  THEN
	       max := Trunc(S(x))
	    ELSE
	       max := Trunc(chLR*x); DEC(max)
	       END
	    END;


	 (* En vue du choix initial de zj.                               *)
	 IF  min > max  THEN
	    RETURN TRUE
	 ELSE
	    zcurrent := min
	    END

      ELSE (* j = Dim *)
	 zcurrent := 1;
	 IF  Stage = 2  THEN
	    max := 1;
	 ELSE
	    zcurrent := 2;
	    max := Trunc(S(Sqrt(S(R2[j]/LDC2[j]))))
	    END
	 END;

      (*-----------------------------------------------------------------*)

      WHILE  zcurrent <= max  DO

	 zLR[j] := LIToLR(zcurrent);

	 (* Calcul de R2[j-1].                                           *)
	 x := chLR*(zLR[j] - center);
	 IF  x > E  THEN
	    x := chLR*(x - E)
	 ELSIF  x < -E  THEN
	    x := chLR*(x + E)
	 ELSE
	    x := 0.0
	    END;
	 R2[j-1] := S(R2[j] - chLR*((chLR*(x*x))*LDC2[j]));

	 IF  j = 1  THEN
	    IF  R2[0] >= 0.0  THEN
	       (* On verifie qu'on a trouve un vecteur plus court.       *)

	       (* On determine d'abord s'il est identique a V[i].        *)
	       idem := TRUE;
	       IF  zLR[Dim] # 1.0  THEN
		  idem := FALSE
	       ELSE
		  k := 1;
		  WHILE  idem AND (k < Dim)  DO
		     IF  zLR[k] # 0.0  THEN  idem := FALSE  END;
		     INC(k)
		     END
		  END;

	       IF  NOT idem  THEN
		  BCopyVect (V[Dim], V[0], Dim);
		  FOR  k := 1  TO  Dim - 1  DO
		     BModifVectLR (V[0], V[k], zLR[k], Dim)
		     END;
		  IF Stage = 3 THEN
		     BModifVectLR (V[0], V[Dim], zLR[Dim] - 1.0, Dim)
		     END;

		  BProdScalSI (V[0], V[0], Dim, S1);

		  IF  Smaller (S1, S2)  THEN
		     IF  (Stage = 2)
			OR ((Stage = 3)
			    AND (GCDvect(zLR, i, Dim) = 1.0))  THEN
			zshort := zLR;
			RETURN FALSE
			END
		     END;

		  IF  Equal (S1, S2) AND
		      ((Stage = 2) OR ((Stage = 3) AND
                      (GCDvect(zLR, i, Dim) = 1.0))) THEN
		     IF  d = 0  THEN
			NEW (basislist);
			lastbasis := basislist
		     ELSE
			NEW (lastbasis^.NextBasis);
			lastbasis := lastbasis^.NextBasis
			END;
		     INC (lengthbasislist);

		     WITH  lastbasis^  DO
			SupToMScal (base^.mSI, tempm);
			InitBasis (base, tempm, base^.Norm, Dim);
			CopyBasis (B, base);
			di := d + 1;
			IF  Stage = 2  THEN
			   k := Dim;
			ELSE
			   FOR  h := 1  TO  Dim  DO
			      zLI[h] := Trunc (zLR[h])
			      END;
			   TransformStage3 (base, zLI, k)
			   END;
			BCopyVect (base^.V[0], base^.V[k], Dim);
			IF  zLI[k] < 0  THEN
			   BChangeSignVect (W[k], Dim)
			   END;
			FOR  h := 1  TO  Dim  DO
			   IF  (zLI[h] # 0) AND (h # k) THEN
			      BModifVectLI (W[h], W[k], -zLI[h], Dim)
			      END
			   END;
			Permute (base, k, i);
			NextBasis := NIL
			END
		     END 
		  END
	       END
	 ELSE  (* j # 1 *)
	    IF  R2[j-1] >= 0.0  THEN
	       IF  NOT VerifZ (B, j-1, E, E1, e, x, mdc, C0, EC0, zLR, R2,
                               LDC2, zshort, Stage, idem, i, zLI, d )  THEN
                   RETURN FALSE
                   END
	       END
	    END;
	 INC (zcurrent)
	 END;  (* WHILE *)
      RETURN TRUE
      END   (* WITH *)
   END VerifZ;

(*-------------------------------------------------------------------------*)

PROCEDURE VerifMinkowski (B : Basis; d : BDim) : BOOLEAN;
   (* Retourne TRUE lorsque la base est reduite.                           *)
   VAR
      i, d1           : BDim;
      idem, equal : BOOLEAN;
      r2, E, E1, e, x, mdc  : LONGREAL;
      C0, EC0 : BASISLR.BMatr;
      zLR, R2, DC2, LDC2, zshort : BASISLR.BVect;
      Stage : INTEGER;
      zLI : BASISLR.VectLI;

(* deplace a l'exterieur - ajmal 15 Nov 1996 
   PROCEDURE VerifZ (j : BDim) : BOOLEAN;
      VAR
         min, max  : LONGINT;
         center    : LONGREAL;
         zcurrent  : LONGINT;
         k, h : BDim;
      BEGIN
      WITH  B^  DO
         center := 0.0;
         IF  j < Dim  THEN
            E := 0.0;
            E1 := 0.0;
            FOR  k := j+1  TO  Dim  DO
               e := C0[j,k]*zLR[k];
               center := center + e;
               E1 := E1 + ABS(e);
               e := S(S(EC0[j,k]*ABS(zLR[k])) + hLR*S(ABS(e)));
               E := E + e
               END;
            center := -center;
            k := Dim - j;
            E := S(S(h2[k]*E) + S(H[k]*E1));

            IF  j = 1  THEN
               x := center - E;
               IF  x > 0.0  THEN
                  min := Trunc(chLR*x);
               ELSE
                  min := Trunc(S(x)); DEC(min)
                  END;
               x := center + E;
               IF  x > 0.0  THEN
                  max := Trunc(S(x)); INC(max)
               ELSE
                  max := Trunc(chLR*x)
                  END
            ELSE

               mdc := S(S(Sqrt(S(R2[j]/LDC2[j]))) + E);

               x := center - mdc;
               IF  x > 0.0  THEN
                  min := Trunc(chLR*x); INC(min)
               ELSE
                  min := Trunc(S(x))
                  END;
               x := center + mdc;
               IF  x > 0.0  THEN
                  max := Trunc(S(x))
               ELSE
                  max := Trunc(chLR*x); DEC(max)
                  END
               END;

            IF  min > max  THEN
               RETURN TRUE
            ELSE
               zcurrent := min
               END

         ELSE 
            zcurrent := 1;
            IF  Stage = 2  THEN
               max := 1;
            ELSE
               zcurrent := 2;
               max := Trunc(S(Sqrt(S(R2[j]/LDC2[j]))))
               END
            END;

         WHILE  zcurrent <= max  DO

            zLR[j] := LIToLR(zcurrent);

            x := chLR*(zLR[j] - center);
            IF  x > E  THEN
               x := chLR*(x - E)
            ELSIF  x < -E  THEN
               x := chLR*(x + E)
            ELSE
               x := 0.0
               END;
            R2[j-1] := S(R2[j] - chLR*((chLR*(x*x))*LDC2[j]));

            IF  j = 1  THEN
               IF  R2[0] >= 0.0  THEN

                  idem := TRUE;
                  IF  zLR[Dim] # 1.0  THEN
                     idem := FALSE
                  ELSE
                     k := 1;
                     WHILE  idem AND (k < Dim)  DO
                        IF  zLR[k] # 0.0  THEN  idem := FALSE  END;
                        INC(k)
                        END
                     END;

                  IF  NOT idem  THEN
                     BCopyVect (V[Dim], V[0], Dim);
                     FOR  k := 1  TO  Dim - 1  DO
                        BModifVectLR (V[0], V[k], zLR[k], Dim)
                        END;
                     IF Stage = 3 THEN
                        BModifVectLR (V[0], V[Dim], zLR[Dim] - 1.0, Dim)
                        END;

                     BProdScalSI (V[0], V[0], Dim, S1);

                     IF  Smaller (S1, S2)  THEN
                        IF  (Stage = 2)
                           OR ((Stage = 3)
                               AND (GCDvect(zLR, i, Dim) = 1.0))  THEN
                           zshort := zLR;
                           RETURN FALSE
                           END
                        END;

                     IF  Equal (S1, S2) AND
                        ((Stage = 2) OR ((Stage = 3) AND (GCDvect(zLR, i, Dim) = 1.0)))
                                                                                        THEN
                        IF  d = 0  THEN
                           NEW (basislist);
                           lastbasis := basislist
                        ELSE
                           NEW (lastbasis^.NextBasis);
                           lastbasis := lastbasis^.NextBasis
                           END;
                        INC (lengthbasislist);

                        WITH  lastbasis^  DO
                           SupToMScal (base^.mSI, tempm);
                           InitBasis (base, tempm, base^.Norm, Dim);
                           CopyBasis (B, base);
                           di := d + 1;
                           IF  Stage = 2  THEN
                              k := Dim;
                           ELSE
                              FOR  h := 1  TO  Dim  DO
                                 zLI[h] := Trunc (zLR[h])
                                 END;
                              TransformStage3 (base, zLI, k)
                              END;
                           BCopyVect (base^.V[0], base^.V[k], Dim);
                           IF  zLI[k] < 0  THEN
                              BChangeSignVect (W[k], Dim)
                              END;
                           FOR  h := 1  TO  Dim  DO
                              IF  (zLI[h] # 0) AND (h # k) THEN
                                 BModifVectLI (W[h], W[k], -zLI[h], Dim)
                                 END
                              END;
                           Permute (base, k, i);
                           NextBasis := NIL
                           END
                        END 
                     END
                  END
            ELSE 
               IF  R2[j-1] >= 0.0  THEN
                  IF  NOT VerifZ(j-1)  THEN RETURN FALSE  END
                  END
               END;
            INC (zcurrent)
            END;  
         RETURN TRUE
         END  
      END VerifZ;
End ajmal *)


   BEGIN
   IF  d = 0  THEN
      lengthbasislist := 0
      END;
   WITH B^ DO
      d1 := (Dim DIV 2) + 1;
      (*  Il faut d'abord verifier que les vecteurs sont en ordre de       *)
      (*  longueurs croissantes.                                           *)
      FOR  i := 1  TO  Dim  DO
         BProdScalSI(V[i], V[i], Dim, VVSI[i]);
         IF  (i>1) AND Smaller(VVSI[i], VVSI[i-1])  THEN
            WriteLn; WriteString ("The basis is not ordered."); WriteLn;
            RETURN FALSE
            END
         END;
       
      Stage:=1;
      WHILE (Stage<3) DO
         Stage := Stage+1;
         IF  (Stage = 2) OR ((Stage = 3) AND (Dim > 7))  THEN 

            (*  On permute circulairement les vecteurs de base de maniere  *)
            (*  que le plus petit apparaisse en dernier.                   *)
            FOR  i := 1  TO  Dim - 1  DO
               Permute (B, i, i+1)
               END;

            i := 0;
            WHILE (i<Dim) DO
               i := i+1;
               (* Un minorant pour le carre de la longueur de V[i].        *)
               BProdScalSI(V[Dim], V[Dim], Dim, S2);
               IntToSup(1, S4);
               r2 := DivideLR(S2, S4, equal);

               (* Un majorant pour le carre de la longueur de V[i].        *)
               IF  NOT equal  THEN
                  R2[Dim] := S(r2)
               ELSE
                  R2[Dim] := r2
                  END;
                
               CalculErr (B, DC2, LDC2, C0, EC0, d1);
               IF  NOT VerifZ(B, Dim, E, E1, e, x, mdc, C0, EC0, zLR, R2, LDC2, zshort, Stage, idem, i, zLI, d )  THEN  RETURN FALSE  END;
               Permute (B, i, Dim)
               END
            END;
         END
      END;

   IF  d # 0  THEN
      IF  currentbasis^.NextBasis # NIL  THEN
         currentbasis := currentbasis^.NextBasis;
         WITH  currentbasis^  DO
            IF  ReductMinkowski (base, di)  THEN
               IF  VerifMinkowski (base, di)  THEN
                  RETURN TRUE
               ELSE
                  RETURN FALSE
                  END
            ELSE
               RETURN FALSE 
               END
            END
         END
      END; 
   RETURN TRUE
   END VerifMinkowski;   

(* ajmal 15 Nov 1996 *)
   PROCEDURE VerifZ0 
      ( B                         : Basis;
        j                         : BDim;
        VAR E, E1, mdc, x, e      : LONGREAL;
        VAR k                     : BDim;
        VAR C0, EC0               : BASISLR.BMatr;
        VAR zLR, R2, LDC2, zshort : BASISLR.BVect;
        VAR idem, FoundZero       : BOOLEAN ) : BOOLEAN;

      (* Retourne TRUE lorsqu'on ne trouve pas de vecteur plus court.       *)
      VAR
         min, max  : LONGINT;
         center    : LONGREAL;
         zcurrent  : LONGINT;
         kprime	   : BDim;
      BEGIN
      WITH  B1^  DO
         (* Calcul d'un intervalle contenant les valeurs admissibles de zj. *)
         (* Il pourrait eventuellement en contenir qui ne le sont pas.      *)
         center := 0.0;

         (* Calcul approximatif du centre de l'intervalle ainsi que         *)
         (* d'un majorant de la valeur absolue de l'erreur commise.         *)
         E := 0.0;
         E1 := 0.0;
         kprime := k;
         FOR  kprime := j+1  TO  Dim  DO
            e := C0[j,kprime]*zLR[kprime];
            center := center + e;
            E1 := E1 + ABS(e);
            e := S(S(EC0[j,kprime]*ABS(zLR[kprime])) + hLR*S(ABS(e)));
            E := E + e
            END;
         center := -center;
         k := Dim - j;
         E := S(S(h2[k]*E) + S(H[k]*E1));

         (* Majorant de la distance du centre approximatif aux           *)
         (* extremites de l'intervalle.                                  *)
         mdc := S(S(Sqrt(S(R2[j]/LDC2[j]))) + E);

         (* Calcul de deux entiers ayant la propriete qu'un entier       *)
         (* non-compris entre (i.e. strictement exterieur `a) ceux-ci    *)
         (* n'appartient pas a l'intervalle.                             *)
         x := center - mdc;
         IF  x > 0.0  THEN
            min := Trunc(chLR*x); INC(min)
         ELSE
            min := Trunc (S(x))
            END;
         x := center + mdc;
         IF  x > 0.0  THEN
            max := Trunc(S(x))
         ELSE
            max := Trunc (chLR*x); DEC(max)
            END;            
            
         IF  NOT FoundZero  THEN
            IF  j > 1  THEN  
               min := 0  
            ELSE
               FoundZero := TRUE;
               min := 1
               END
            END;

         (* En vue du choix initial de zj.                               *)  
         IF  min > max  THEN  
            RETURN TRUE
         ELSE  
            zcurrent := min
            END;

         (*-----------------------------------------------------------------*)

         WHILE  zcurrent <= max  DO
            zLR[j] := LIToLR(zcurrent);  

            (* Calcul de R2[j-1].                                           *) 
            x := chLR*(zLR[j] - center);
            IF  x > E  THEN
               x := chLR*(x - E);
            ELSIF  x < -E  THEN
               x := chLR*(x + E)
            ELSE
               x := 0.0
               END;
            R2[j-1] := S(R2[j] - chLR*((chLR*(x*x))*LDC2[j]));

            IF  j = 1  THEN   
               IF  R2[0] >= 0.0  THEN
                  (* On verifie qu'on a trouve un vecteur plus court.       *)

                  (* On determine d'abord s'il est identique a + ou -V1.    *)
                  idem := TRUE;
                  IF  ABS(zLR[1]) # 1.0  THEN  
                     idem := FALSE
                  ELSE
                     k := 2;
                     WHILE  idem AND (k <= Dim)  DO
                        IF  zLR[k] # 0.0  THEN  idem := FALSE  END;
                        INC(k)
                        END
                     END;   

                  IF  NOT idem  THEN
                     (* Fait V[0] egal a 0. *)
                     BCopyVect(BZeroVect, V[0], Dim);

                     FOR  kprime := 1  TO  Dim  DO
                        BModifVectLR(V[0], V[kprime], zLR[kprime], Dim)
                        END;

                     BProdScalSI(V[0], V[0], Dim, S1);
                     IF  Smaller(S1, S2)  THEN
                        zshort := zLR;
                        RETURN FALSE
                        END                 
                     END
                  END
            ELSE  (* j # 1 *)
               IF  R2[j-1] >= 0.0  THEN
(* ajmal 15 Nov 1996                                             *)
(*                  IF  NOT VerifZ0(j-1)  THEN RETURN FALSE  END *)
                  IF  NOT VerifZ0(B, j-1, E, E1, mdc, x, e, k, C0, EC0, zLR, R2, LDC2, zshort, idem, FoundZero )  THEN RETURN FALSE  END
                  END
               END;
            INC(zcurrent)
            END;  (* WHILE *)
         RETURN TRUE
         END   (* WITH *)
      END VerifZ0;

PROCEDURE VerifShortest (B : Basis) : BOOLEAN;
   (* Retourne TRUE lorsque le premier vecteur de la base est le plus petit.*)

   VAR
      k, d1           : BDim;
      zLR, R2, zshort,
      DC2, LDC2       : BASISLR.BVect;
      E, E1, mdc,
      x, e            : LONGREAL;
      idem, FoundZero, equal : BOOLEAN;
      C0, EC0         : BASISLR.BMatr;

(* deplace a l'exterieur - ajmal 15 Nov 1996 
   PROCEDURE VerifZ0 (j : BDim) : BOOLEAN;
      VAR
         min, max  : LONGINT;
         center    : LONGREAL;
         zcurrent  : LONGINT;
      BEGIN
      WITH  B1^  DO
         center := 0.0;

         E := 0.0;
         E1 := 0.0;
         FOR  k := j+1  TO  Dim  DO
            e := C0[j,k]*zLR[k];
            center := center + e;
            E1 := E1 + ABS(e);
            e := S(S(EC0[j,k]*ABS(zLR[k])) + hLR*S(ABS(e)));
            E := E + e
            END;
         center := -center;
         k := Dim - j;
         E := S(S(h2[k]*E) + S(H[k]*E1));

         mdc := S(S(Sqrt(S(R2[j]/LDC2[j]))) + E);

         x := center - mdc;
         IF  x > 0.0  THEN
            min := Trunc(chLR*x); INC(min)
         ELSE
            min := Trunc (S(x))
            END;
         x := center + mdc;
         IF  x > 0.0  THEN
            max := Trunc(S(x))
         ELSE
            max := Trunc (chLR*x); DEC(max)
            END;            
            
         IF  NOT FoundZero  THEN
            IF  j > 1  THEN  
               min := 0  
            ELSE
               FoundZero := TRUE;
               min := 1
               END
            END;
   
         IF  min > max  THEN  
            RETURN TRUE
         ELSE  
            zcurrent := min
            END;

         WHILE  zcurrent <= max  DO
            zLR[j] := LIToLR(zcurrent);  

            x := chLR*(zLR[j] - center);
            IF  x > E  THEN
               x := chLR*(x - E);
            ELSIF  x < -E  THEN
               x := chLR*(x + E)
            ELSE
               x := 0.0
               END;
            R2[j-1] := S(R2[j] - chLR*((chLR*(x*x))*LDC2[j]));

            IF  j = 1  THEN   
               IF  R2[0] >= 0.0  THEN

                  idem := TRUE;
                  IF  ABS(zLR[1]) # 1.0  THEN  
                     idem := FALSE
                  ELSE
                     k := 2;
                     WHILE  idem AND (k <= Dim)  DO
                        IF  zLR[k] # 0.0  THEN  idem := FALSE  END;
                        INC(k)
                        END
                     END;   

                  IF  NOT idem  THEN
                     BCopyVect(BZeroVect, V[0], Dim);

                     FOR  k := 1  TO  Dim  DO
                        BModifVectLR(V[0], V[k], zLR[k], Dim)
                        END;

                     BProdScalSI(V[0], V[0], Dim, S1);
                     IF  Smaller(S1, S2)  THEN
                        zshort := zLR;
                        RETURN FALSE
                        END                 
                     END
                  END
            ELSE
               IF  R2[j-1] >= 0.0  THEN
                 IF  NOT VerifZ0(j-1)  THEN RETURN FALSE  END
                  END
               END;
            INC(zcurrent)
            END;
         RETURN TRUE
         END
      END VerifZ0;
End ajmal *)

   BEGIN
   CopyBasis (B, B1);
   WITH  B1^  DO
      d1 := (Dim DIV 2) + 1;
      BProdScalSI(V[1], V[1], Dim, S2);
      IntToSup(1, S4);
      R2[Dim] := DivideLR(S2, S4, equal);
      R2[Dim] := S(R2[Dim]);

      CalculErr (B1, DC2, LDC2, C0, EC0, d1);
      FoundZero := FALSE;

(* ajmal 15 Nov 1996         *)
(*      RETURN  VerifZ0(Dim) *)
      RETURN  VerifZ0(B, Dim, E, E1, mdc, x, e, k, C0, EC0, zLR, R2, LDC2, zshort, idem, FoundZero )
      END
   END VerifShortest;

PROCEDURE ReductVerifMinkowski (B : Basis) : BOOLEAN;
   BEGIN
   IF  ReductMinkowski (B, 0)  THEN
      IF  VerifMinkowski (B, 0)  THEN  RETURN TRUE  ELSE  RETURN FALSE  END
   ELSE
      RETURN FALSE
      END
   END ReductVerifMinkowski;

PROCEDURE ShortestVectorVerif (B : Basis) : BOOLEAN;
   BEGIN
   IF  ShortestVector (B)  THEN
      IF  ShortestVectorVerif (B)  THEN  RETURN TRUE  ELSE  RETURN FALSE  END
   ELSE
      RETURN FALSE
      END
   END ShortestVectorVerif;

PROCEDURE InitREDBAS2 (d : BDim);
   VAR
      i, d1 : BDim;
      temp : MScal;
   BEGIN
   IF  d > curmaxdim  THEN
      IF  curmaxdim = 0  THEN  d1 := 0  ELSE  d1 := curmaxdim + 1  END;
      SupToMScal (B1^.mSI, temp);
      InitBasis (B1, temp, B1^.Norm, d1);
      BCreateVect (BZeroVect, d1, d);
      FOR  i := d1  TO  d  DO  BAffect (BZero, BZeroVect[i]) END
      END
   END InitREDBAS2;


BEGIN
curmaxdim := 0;
CreateBasis (B1);
Create (S1, 0);  Create (S2, 0);  Create (S4, 0);

(*************************Majorants et minorants****************************)

h[1] := 0.0;
h[2] := hLR;
h2[1] := 1.0;
h2[2] := S(1.0);
H[1] := 0.0;
H[2] := S(hLR);
FOR  l := 3  TO  BMaxDim  DO
   (* Majoration de h_l.                                                   *)
   h[l] := S(S(IToLR(l-2)*hLR + 1.0)*IToLR(l-1))*hLR;
   (* Majoration de 1/(1 - h_l).                                           *)
   h2[l] := S(1.0 + h[l]);
   (* Majoration de h_l/(1 - h_l).                                         *)
   H[l] := S(h[l] + S(h[l]*h[l]))
   END;
FOR  l := 2  TO  BMaxDim  DO
   (* Majoration de h/(1 - h) 1/(1 - h_l) + h_l/(1 - h_l)                  *)
   h3[l] := S(S(H[2]*h2[l]) +  H[l]);
   (* Minorant de 1/(1 + h_l).                                             *)
   i1h[l] := chLR*(1.0 - h[l])
   END

END REDBAS2.

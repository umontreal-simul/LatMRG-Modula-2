IMPLEMENTATION MODULE PRIM;
FROM SUPINT   IMPORT SuperInteger, Create, Affect, WriteSup;
FROM SUPARITH IMPORT Equal, GCD, PowerSupInt, Quotient, Subtract, Add, Greater,
                     Smaller, Negative, Even;
FROM SUPCONV  IMPORT IntToSup, SupToCard;
FROM SUPFACT  IMPORT IsPrime, Factorize, Factors;
FROM MYINOUT  IMPORT WriteString, WriteInt, WriteLn, OpenAsOutput, CloseOutput;
FROM NUM      IMPORT WriteLI;
FROM MYPARAM  IMPORT ParamToString, HostName;
FROM CHRONO   IMPORT Chrono, InitChrono, WriteChrono, hms;

VAR
   (*  Sm, Smm1 : ARRAY [0..J] OF SuperInteger;  *)
   One, Two, ST, STm1, STs2, Smk, Sm0, Sm1, Sm2, Sdiff : SuperInteger;
   m, n     : LONGINT;
   i, k     : INTEGER;
   L1, L2   : Factors;
   machine  : ARRAY[0..255] OF CHAR;
   C        : Chrono;

PROCEDURE Trier (VAR L : Factors);
   (* Trie les facteurs de la liste de L en ordre DECROISSANT. *)
   VAR
      T,
      PrecF, CurF,
      PrecPG, CurPG,
      PrecH, CurH, NextH : Factors;
   BEGIN
   (* L # NIL. *)
   PrecH := NIL;  CurH := L;  NextH := CurH^.Next;
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

(*

CONST
   J    = 4;

PROCEDURE TryThesem (m0, K, Skip : LONGINT;  j : INTEGER);
   (*  Prints the largest integers m_j < ... < m_1 <= m such that
       $m_j <= m_{j-1} - Skip$ for each j, 
       lcm $(m_1, ... , m_j) = m_1 \times ... \times m_j / 2^{j-1}$.  
       Repeats this for each m between m0-K and m0.                    *)
   VAR
      m : LONGINT;
   BEGIN
   IF j > J THEN j := J END;
   FOR m := m0 TO (m0 - K) BY -2 DO
      IntToSup (m, Sm [j]);
      IF IsPrime (Sm [j], 100) THEN
         IntToSup (m-1, Smm1 [j]);
         GCD (Smm1 [j], Smm1 [j-1], ST);
         IF Equal (ST, Two) THEN
            IF j < J THEN
               TryThesem (m - Skip, j+1)
            ELSE
               FOR i := 1 TO J DO
                  WriteSup (Sm [i], 10, 50);  WriteString ("  ");
                  END;
               WriteLn
               END
            END
         END
      END
   END TryThesem;

*)

PROCEDURE SFindPrimer (k, e : LONGINT;  S1, S2 : SuperInteger;  
                       Safe : BOOLEAN);
   (*  Finds and prints all primes m such that S1 <= m <= S2 and    
       r = (m^k-1)/(m-1) is prime. 
       If Safe = TRUE, it is also required that $(m-1) / 2$ be prime.
       If k=1, then r is considered always prime.  
       The retained m are printed in the form  m = 2^e +/- x,
       in decreasing order.
       The factors of m-1 are also printed.                            *)
   VAR
      j  : CARDINAL;
   BEGIN
   Affect (One, Smk);
   PowerSupInt (Two, e, Sm0); 
   IF Even (S2) THEN Subtract (S2, One, S2) END; 
   Affect (S2, ST);
   WHILE (NOT Smaller (ST, S1)) DO   
      IF IsPrime (ST, 200) THEN
         Subtract (ST, One, STm1);
         Quotient (STm1, Two, STs2); 
         IF k > 1 THEN
            PowerSupInt (ST, k, Smk);  Subtract (Smk, One, Smk);
            Quotient (Smk, STm1, Smk);
            END;
         (* Ici:   m   = ST,                              *)
         (*        m-1 = STm1,   (m-1)/2 = STs2,          *)
         (*        r   = (m^k-1)/(m-1) = Smk.             *)
         IF ((k = 1) OR IsPrime (Smk, 200)) AND 
               ((NOT Safe) OR IsPrime (STs2, 100)) THEN
            WriteString (" m = ");
            WriteSup (ST, 10, 70);  WriteLn;  
            Subtract (ST, Sm0, Sdiff); 
            WriteString ("   = 2^");  WriteLI (e, 2);
            IF (NOT Negative (Sdiff)) THEN   WriteString (" + ") END;
            WriteSup (Sdiff, 10, 70);  WriteLn;
            Factorize (STm1, 10.0, L1);   Trier (L1);
            WriteString ("   Factors of m-1: "); 
            WHILE L1 # NIL DO
               FOR j := 1 TO L1^.Multiplicity DO
                  WriteSup (L1^.Factor, 10, 50);  WriteString (", ");
                  END;
               L1 := L1^.Next
               END;
            WriteLn;
            END;
         END;
      Subtract (ST, Two, ST);
      END
   END SFindPrimer;

PROCEDURE FindPrimer (k, m0, m1 : LONGINT;  Safe : BOOLEAN);
   (*  Similar to SFindPrimemr, but for values of m less than 2^{31}.   *)
   VAR
      m : LONGINT;
      j : CARDINAL;
   BEGIN
   Affect (One, Smk);
   IF (NOT ODD (m1)) THEN m1 := m1 - 1 END;
   FOR m := m1 TO m0 BY -2 DO
      IntToSup (m, ST);   
      IF IsPrime (ST, 100) THEN
         IntToSup (m-1, STm1);
         Quotient (STm1, Two, STs2); 
         IF k > 1 THEN
            PowerSupInt (STm1, k, Smk);  Subtract (Smk, One, Smk);
            Quotient (Smk, STs2, Smk);
            END;
         IF ((k = 1) OR IsPrime (Smk, 200)) AND 
               ((NOT Safe) OR IsPrime (STs2, 100)) THEN
            WriteSup (ST, 10, 50);  WriteLn;
            Factorize (STm1, 10.0, L1);   Trier (L1);
            WriteString ("   Factors of m-1: "); 
            WHILE L1 # NIL DO
               FOR j := 1 TO L1^.Multiplicity DO
                  WriteSup (L1^.Factor, 10, 50);  WriteString (", ");
                  END;
               L1 := L1^.Next
               END;
            WriteLn;
            END
         END
      END
   END FindPrimer;

PROCEDURE FindPrimesmr 
      (k, e, c1, c2 : LONGINT;  Safe : BOOLEAN;   F : ARRAY OF CHAR);
   (* Finds all $m$ such that $2^e + c1 <= m <= 2^e + c2$, $m$ is prime,
      and $r = (m^k-1) / (m-1)$ is prime.  If Safe = TRUE, it is also
      required that $(m-1) / 2$ be prime.
      Prints the results in the file F.                                   *)
   BEGIN
   OpenAsOutput (F);
   HostName (machine);
   WriteString ('Tests are running on : ');  
   WriteString (machine);  WriteLn;  WriteLn;
   WriteString ("Values such that m");
   IF Safe THEN WriteString (", (m-1)/2,") END;
   WriteString (" and $(m^k-1)/(m-1)$ are prime.");
   WriteLn;  WriteString ("k = ");  WriteInt (k, 2);  WriteLn;
   WriteString ("e = ");  WriteInt (e, 2);
   WriteString (",  c1 = ");  WriteInt (c1, 2); 
   WriteString (",  c2 = ");  WriteInt (c2, 2);  WriteLn;
   InitChrono (C);
   PowerSupInt (Two, e, Sm0);  
   IntToSup (c1, ST);  Add (Sm0, ST, Sm1);
   IntToSup (c2, ST);  Add (Sm0, ST, Sm2);
   WriteString ("  m from 2^");  WriteInt (e, 1); 
   IF (c1 >= 0) THEN WriteString (" + ") ELSE WriteString (" ") END;  
   WriteLI (c1, 1); 
   WriteString (" to 2^");   WriteInt (e, 1);
   IF (c2 >= 0) THEN WriteString (" + ") ELSE WriteString (" ") END;  
   WriteLI (c2, 1);   WriteLn;  WriteLn;
   (* Sm1 = 2^e + c1,  Sm2 = 2^e + c2.   *)
   SFindPrimer (k, e, Sm1, Sm2, Safe);
   WriteLn;  WriteLn;
   WriteString ("CPU time: ");  WriteChrono (C, hms);
   CloseOutput;
   END FindPrimesmr;

BEGIN
(*  FOR i := 0 TO J DO  Create (Sm [i], 2);   Create (Smm1 [i], 2)  END;  *)
(*  IntToSup (2, Smm1 [0]);   *)
Create (One, 1);  Create (Two, 1);
Create (ST, 2);   Create (STm1, 2);  Create (STs2, 2);  Create (Smk, 4);
Create (Sm0, 4);  Create (Sm1, 4);   Create (Sm2, 4);   Create (Sdiff, 4);
IntToSup (1, One);  IntToSup (2, Two); 
END PRIM.




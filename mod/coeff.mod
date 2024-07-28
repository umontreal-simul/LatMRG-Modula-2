MODULE coeff;

FROM MYINOUT IMPORT WriteLn, WriteString, WriteCard, WriteInt, WriteBool, WriteLongReal,
                    ReadLn, ReadString, ReadCard, ReadInt, ReadBool,WriteLongInt,
                    OpenInput, CloseInput, OpenOutput, CloseOutput, ReadLongInt, SetOutput,
                    OpenAsOutput, GetOutput, FILE;
FROM MYSTR   IMPORT Append, Length;
FROM NUM     IMPORT LIToLR;
FROM TABLES  IMPORT TabLR, CreateTab, DeleteTab, LR;
FROM PALPHA  IMPORT CaractGenerateur,SaisieDonnees,CalculPAlpha2,CalculPAlpha4,
                    CalculPAlpha6, CalculPAlpha8, PeriodeMax, EcritPBAlpha,PAlpha2PerNonMax,
                    CalculBAlpha2, EcritEntete, EcritDonnees, InitTab, SortTab, MakeInterv,
                    PAlpha4PerNonMax, PAlpha6PerNonMax, PAlpha8PerNonMax;

VAR Gen : CaractGenerateur; 
    PAlpha, BestPAlpha, TotalPAlpha : LONGREAL;
    Dim,i : INTEGER;
    Indice : INTEGER;
    Coefficient, BestCoeff : INTEGER;
    PtrTabUij, TablePAl : TabLR;
    TotalGen : LONGINT;
    FichSortie : FILE;
    Nom : ARRAY[1..32] OF CHAR;
BEGIN
  
  (*Ouverture du fichier contenant les parametres*)
  OpenInput(".dat");    
  
  (*Lecture des parametres*)
  SaisieDonnees(Gen);
   
  (*Fermeture du fichier contenant les parametres*)
  CloseInput;
  
  (*Ouverture des fichiers de sortie*)
  OpenOutput(".res");
  GetOutput(FichSortie);  

  SetOutput(FichSortie);  
  EcritEntete;
  EcritDonnees(Gen);


  (*Execution du calcul demande*) 
  FOR Dim := Gen.Min TO Gen.Max DO
    IF ((Dim - Gen.Min) MOD Gen.Saut)= 0 THEN   
      CreateTab(PtrTabUij, LR, Dim-1);
      BestPAlpha := 10000000.0;
      TotalPAlpha := 0.0;
      TotalGen := 0;
      BestCoeff := Gen.BorneInfA;
      CreateTab(TablePAl, LR, Gen.BorneSupA);
      InitTab(TablePAl, Gen.BorneSupA);

      (* SI LE MODULO EST UN NOMBRE PREMIER *) 
      IF Gen.Prime THEN
        FOR Coefficient:= Gen.BorneInfA TO Gen.BorneSupA DO        
          Gen.A := Coefficient;
          (* La periode est max, ce a est considere ds tous les cas*)
          IF PeriodeMax(Gen) THEN  
            TotalGen := TotalGen + 1;               
            CASE Gen.Alpha OF
             2 : PAlpha := CalculPAlpha2(Gen, Dim, PtrTabUij);     
            |4 : PAlpha := CalculPAlpha4(Gen, Dim, PtrTabUij);  
            |6 : PAlpha := CalculPAlpha6(Gen, Dim, PtrTabUij);
            |8 : PAlpha := CalculPAlpha8(Gen, Dim, PtrTabUij); 
            ELSE
              WriteString(" Le alpha donne n'est pas valide pour effectuer le calcul."); 
              WriteLn; 
            END;
            TotalPAlpha := TotalPAlpha + PAlpha;
            TablePAl^[Coefficient-1] := PAlpha;                
            IF PAlpha < BestPAlpha THEN  
              BestPAlpha := PAlpha;
              BestCoeff := Coefficient; 
            END;   
          (* Periode non max mais ce n'est pas requis *) 
          ELSIF NOT(Gen.PeriodeMax) AND NOT(PeriodeMax(Gen)) THEN
            TotalGen := TotalGen + 1;  
            CASE Gen.Alpha OF
             2 : PAlpha := PAlpha2PerNonMax(Gen, Dim);     
            |4 : PAlpha := PAlpha4PerNonMax(Gen, Dim);
            |6 : PAlpha := PAlpha6PerNonMax(Gen, Dim);
            |8 : PAlpha := PAlpha8PerNonMax(Gen, Dim);
            ELSE
              WriteString(" Le alpha donne n'est pas valide pour effectuer le calcul."); 
              WriteLn; 
            END; 
            TotalPAlpha := TotalPAlpha + PAlpha;
            TablePAl^[Coefficient-1] := PAlpha;                
            IF PAlpha < BestPAlpha THEN  
              BestPAlpha := PAlpha;
              BestCoeff := Coefficient; 
            END;  
          END;                
        END;

      (* SI LE MODULO N'EST PAS UN NOMBRE PREMIER, de preference une
         puissance de 2 *) 
      ELSE
        FOR Coefficient:= 3 TO Gen.BorneSupA BY 2 DO        
          Gen.A := Coefficient;          
          TotalGen := TotalGen + 1;               
          CASE Gen.Alpha OF
           2 : PAlpha := PAlpha2PerNonMax(Gen, Dim);     
          |4 : PAlpha := PAlpha4PerNonMax(Gen, Dim);  
          |6 : PAlpha := PAlpha6PerNonMax(Gen, Dim);
          |8 : PAlpha := PAlpha8PerNonMax(Gen, Dim);
          ELSE
            WriteString(" Le alpha donne n'est pas valide pour effectuer le calcul."); 
            WriteLn; 
          END;
          TotalPAlpha := TotalPAlpha + PAlpha;
          TablePAl^[Coefficient-1] := PAlpha;                
          IF PAlpha < BestPAlpha THEN  
            BestPAlpha := PAlpha;
            BestCoeff := Coefficient; 
          END; 
        END;
      END;

      SortTab(TablePAl, Gen.BorneSupA);         
      MakeInterv(TablePAl, Gen.BorneSupA);

      SetOutput(FichSortie);      
      (*Ecriture des resultats dans le fichier *)  
      WriteString(" Dimension ");
      WriteInt(Dim,2);
      WriteString("\\");
      WriteLn;

      WriteString(" Meilleur A : ");
      WriteInt(BestCoeff,3);
      WriteString("\\");
      WriteLn;

      WriteString(" $P_{\alpha}$ de : ");
      WriteLongReal(BestPAlpha,3,3);
      WriteString("\\");
      WriteLn;

      IF Gen.Alpha = 2 THEN
        WriteString(" $B_{\alpha}$ de : ");
        WriteLongReal(CalculBAlpha2(Gen,Dim),3,3);
        WriteString("\\");
        WriteLn;
      END;     

      TotalPAlpha := TotalPAlpha/(LIToLR(TotalGen)); 
      WriteString(" $P_{\alpha}$ moyen de : ");
      WriteLongReal(TotalPAlpha,3,3);
      WriteString("\\");
      WriteLn;
    
      WriteString(" $P_{\alpha}$ normalise de : ");
      WriteLongReal(BestPAlpha/TotalPAlpha,3,3);
      WriteString("\\ \\");
      WriteLn;
      DeleteTab(PtrTabUij, LR, Dim-1);
      DeleteTab(TablePAl, LR, Gen.BorneSupA);
    END;
  END; 
  WriteLn; 
  (*Fermeture du fichier de sortie*)
  DeleteTab(Gen.TabBeta, LR, Gen.Max +1);
  WriteString("\end{document}");
  CloseOutput;
 
END coeff.


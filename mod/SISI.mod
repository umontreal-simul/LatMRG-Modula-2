IMPLEMENTATION MODULE SISI;

FROM SUPINT  IMPORT SuperInteger, Affect;
FROM MULTSI  IMPORT MScal;             (* SuperInteger.                   *)
FROM BASISSI IMPORT BScal;             (* SuperInteger.                   *)


PROCEDURE MScalToBScal (S : MScal;  VAR R : BScal);
   BEGIN  Affect (S, R)  END MScalToBScal;

PROCEDURE BScalToMScal (S : BScal;  VAR R : MScal);
   BEGIN  Affect (S, R)  END BScalToMScal;

PROCEDURE SupToBScal (S : SuperInteger; VAR R : BScal);
   BEGIN  Affect(S, R)  END SupToBScal;

PROCEDURE SupToMScal (S : SuperInteger; VAR R : MScal);
   BEGIN  Affect(S, R)  END SupToMScal;

PROCEDURE BScalToSup (S : BScal; R : SuperInteger);
   BEGIN  Affect (S, R)  END BScalToSup;

PROCEDURE MScalToSup (S : MScal; R : SuperInteger);
   BEGIN  Affect (S, R)  END MScalToSup;

END SISI.

R = QQ[x, y];

I = ideal(x^2 + y^2 - 1);

G = groebnerBasis I;

G

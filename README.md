# CASymba

🇺🇸 A **CAS engine** (symbolic math) for the TI-84 Plus CE / TI-83 Premium CE calculators  
🇫🇷 *Un moteur de **calcul formel (CAS)** pour les calculatrices TI-84 Plus CE / TI-83 Premium CE*

**Source code**: https://github.com/Hamza-STI/CASYMBA/

**Download**: https://tiplanet.org/forum/archives_voir.php?id=3123911

## License
<a rel="license" href="https://creativecommons.org/licenses/by-nc-sa/4.0/">Creative Commons Attribution-NonCommercial-ShareAlike 4.0<br>
<img alt="Creative Commons License" style="border-width:0" src="https://i.creativecommons.org/l/by-nc-sa/4.0/88x31.png" /></a>


# Presentation :

CASymba est un petit programme de calcul formel destiné aux calculatrices TI-83 Premium CE et TI-84 Plus CE.
Il permet de faire : 
1. de la simplification symbolique
2. calcul de dérivée
3. calcul de dérivée n-ième
4. calcul de dérivée partielle à 2 variables
5. certaines primitives (incomplet)
6. équation de la tangente en un point
7. développement limité / Taylor (***uniquement ce que j'ai vu en étude***)
8. résolution d'équation différentielle d'ordre 1 (avec ou sans conditions - ***uniquement ce que j'ai vu en étude***)
9. résolution d'équation différentielle d'ordre 2 coefficient costant (avec ou sans conditions - ***uniquement ce que j'ai vu en étude***)
10. reste d'une division euclidienne de 2 polynômes
11. pgcd d'une division euclidienne de 2 polynômes
12. quotient d'une division euclidienne de 2 polynômes
13. simplification d'une division de 2 polynômes
14. développement d'expression
15. factorisation de certains polynômes et décomposition en facteur premier (un entier)


# Prérequis

- OS 5.3 ou supérieure. Si la version est 5.5 ou supérieure, il faut activer l'assembleur avec [arTIfiCE](https://yvantt.github.io/arTIfiCE/) + [AsmHook](https://tiplanet.org/forum/archives_voir.php?id=2643391).
- Il faut transférer le programme en mémoire d'Archive.
- Il faut les [bibliothèques C CE](https://github.com/CE-Programming/libraries/releases/tag/v10.2)


# Guide

Saisissez l'expression sous forme de chaîne de caractères, c'est-à-dire commencer la ligne par un guillemet, exemple : `"X+X+X"`
ensuite exécuter le programme CASYMBA: `prgmCASYMBA`.

## Calcul de dérivées 

Utilisez la fonction `nDeriv(` ***calculatrice en anglais*** ou `nbreDérivé(` ***calculatrice en Français*** accessible en appuyant sur la touche `math`.

La fonction prend 3 arguments : `nDeriv(EXPRESSION,VARIABLE,VARIABLE)` ou `nDeriv(EXPRESSION,VARIABLE1,VARIABLE2)` ou `nDeriv(EXPRESSION,VARIABLE,ENTIER_POSITIF)`

### Derivée <img src="https://i.imgur.com/VZp2Tg8.png" align="right"> 

Pour calculer la dérivée de `x*sin(2*x)` : 
```
"nDeriv(X*sin(2*X),X,X)"
prgmCASYMBA
```

<br><br>

### Dérivée n-ième

<img src="https://i.imgur.com/7zlKCTm.png" align="right">

Pour calculer la dérivée seconde de `x*sin(2*x)` : 
```
"nDeriv(X*sin(2*X),X,2)"
prgmCASYMBA
```

<br><br><br>

### Dérivée partielle à 2 variables

<img src="https://i.imgur.com/NpmRtW0.png" align="right">

Pour calculer la dérivée partielle de `y*sin(2*x)` : 
```
"nDeriv(Y*sin(2*X),X,Y)"
prgmCASYMBA
```

<br><br><br><br><br>

## Calcul de (***certaines***) primitives

<img src="https://i.imgur.com/dClTOJc.png" align="right">

***C'est un trop gros programme qui demande de la patience et des connaissances, je n'ai pas encore les moyens de créer quelque chose de complet pour ces modèles***

Utilisez la fonction `fnInt(` ***calculatrice en anglais*** ou `intégrFonct(` ***calculatrice en Français*** accessible en appuyant sur la touche `math`

La fonction prend 4 arguments  : `fnInt(EXPRESSION,VARIABLE,VARIABLE,VARIABLE)`

Pour calculer la primitive de `x*exp(x)` : 
```
"fnInt(X*e^(X),X,X,X)"
prgmCASYMBA
```

## Tangente en un point

<img src="https://i.imgur.com/xiVhNgc.png" align="right">

Utilisez la fonction `Tangent(` ***calculatrice en anglais*** ou `Tangente(` ***calculatrice en Français***

La fonction prend 3 arguments : `Tangent(EXPRESSION,VARIABLE,POINT)`

Pour calculer la tangente de `ln(x)` au point 1 : 
```
"Tangent(ln(X),X,1)"
prgmCASYMBA
```

<br>

## Développment limité / Taylor

<img src="https://i.imgur.com/nBTwGN6.png" align="right">

***(il n'y a pas de fonction se rapprochant niveau nom)***

Utilisez la fonction `det(` ***calculatrice en anglais*** ou `dét(` ***calculatrice en Français*** 

La fonction prend 4 arguments : `det(EXPRESSION,VARIABLE,ORDRE,POINT)`

Pour calculer le dévéloppement limité de `sin(x)` d'ordre 3 au point 0 :
```
"det(sin(X),X,3,0)"
prgmCASYMBA
```

<br>

## Equation différentielle 

La résolution d'équation différentielle linéaire d'ordre 1 et 2.

Utilisez la fonction `solve(` ***calculatrice en anglais*** ou `résoudre(` ***calculatrice en Français***

La fonction prend 3 arguments : `solve(EXPRESSION,VARIABLE1,VARIABLE2)`

**Remarques : les équations doivent être sous la forme suivante AY'+BY=f(X) ou AY''+BY'+CY=f(X)**

### Ordre 1

<img src="https://i.imgur.com/I7RHeL8.png" align="right">

Pour résoudre l'équation différentielle d'ordre 1 de `Y'+2Y=2*e^(-2X)` sans condition :

```
"solve(Y'+2Y=2*e^(-2X),X,Y)"
prgmCASYMBA
```

Pour résoudre l'équation différentielle d'ordre 1 de `Y'+2Y=2*e^(-2X)` avec `Y(0)=1` : 

```
"solve(Y'+2Y=2*e^(-2X) and Y(0)=1,X,Y)"
prgmCASYMBA
```

### Ordre 2

<img src="https://i.imgur.com/M0v07uv.png" align="right">

Pour résoudre l'équa diff d'ordre 2 de `Y''+2Y'+Y=2*e^(-X)` sans les conditions :

```
"solve(Y''+2Y'+Y=2*e^(-X),X,Y)"
prgmCASYMBA
```

**Remarque : il est possible de faire `Y''+2Y'+Y=0` puis `Y''+2Y'+Y=2*e^(-X)`**
 
<br><br><br><br><br>
 
<img src="https://i.imgur.com/ynDPIK7.png" align="right">

Pour résoudre l'équa diff d'ordre 2 de `Y''+2Y'+Y=2*e^(-X)` avec les conditions `f(0) = -1` et `f'(0) = 1` :
```
"solve(Y''+2Y'+Y=2*e^(-X) and Y(0)=-1 and Y'(0)=1,X,Y)"
prgmCASYMBA
```

<br><br><br><br>

## Polynômes

Quelques fonctions pour la division de 2 polynômes

Pour l'exemple par fonction : poly1 = `X^3-6X^2+11X-6` et poly2 = `X^2-6X+8`

### Reste de 2 polynômes <img src="https://i.imgur.com/HuFX6JR.png" align="right">

Utilisez la fonction `remainder(` ***calculatrice en anglais*** ou `reste(` ***calculatrice en Français***

La fonction prend 3 arguments : `remainder(POLY1,POLY2,VARIABLE)`

Pour calculer le reste d'une division euclidienne de 2 polynômes poly1 et poly2 : 
```
"remainder(X^3-6X^2+11X-6,X^2-6X+8,X)"
prgmCASYMBA
```

### PGCD de 2 polynômes

<img src="https://i.imgur.com/IW6qkV1.png" align="right">

Utilisez la fonction `gcd(` ***calculatrice en anglais*** ou `pgcd(` ***calculatrice en Français***

La fonction prend 3 arguments : `gcd(POLY1,POLY2,VARIABLE)`

Pour calculer le pgcd d'une division euclidienne de 2 polynômes poly1 et poly2 : 
```
"gcd(X^3-6X^2+11X-6,X^2-6X+8,X)"
prgmCASYMBA
```

### Quotient de 2 polynômes

<img src="https://i.imgur.com/uHbSZvr.png" align="right">

Utilisez la fonction `int(` ***calculatrice en anglais*** ou `partEnt(` ***calculatrice en Français***

La fonction prend 3 arguments : `int(POLY1,POLY2,VARIABLE)`

Pour calculer le quotient d'une division euclidienne de 2 polynômes poly1 et poly2 : 
```
"int(X^3-6X^2+11X-6,X^2-6X+8,X)"
prgmCASYMBA
```

### Simplification d'une division de 2 polynômes

<img src="https://i.imgur.com/Y8suYn5.png" align="right">

Utilisez la fonction `expr(`

La fonction prend 3 arguments : `expr(POLY1,POLY2,VARIABLE)`

Pour simplifier la division des polynômes poly1 et poly2 : 
```
"expr(X^3-6X^2+11X-6,X^2-6X+8,X)"
prgmCASYMBA
```

<br>

## Développement

<img src="https://i.imgur.com/h0Us6sQ.png" align="right">

Utilisez la fonction `stdDev(` ***calculatrice en anglais*** ou `écart-type(` ***calculatrice en Français***

***(navré pour le choix de la fonction, std fait penser à standard et Dev développement mais en français ça ne fait penser à rien)***
```
"stdDev((A+B)^2)"
prgmCASYMBA
```

<br>

## Décomposer un nombre en facteur premier et factorisation de polynômes

<img src=https://i.imgur.com/oKKuTeK.png align="right">

Utilisez la fonction `identity(` ***calculatrice en anglais*** ou `unité(` ***calculatrice en Français***

La fonction prend en argument un nombre entier (idéalement positif)
```
"identity(45)"
prgmCASYMBA
```

<br>












<img src="https://imgur.com/545YAvK.png" align="right">

Pour la factorisation de polynômes : ***(seulement pour certains polynômes)***

```
"identity(X^5+6X^4+10X^3-4X^2-24X-6,X)"
prgmCASYMBA
```

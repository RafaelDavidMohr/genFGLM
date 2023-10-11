using genFGLM
P, (x,y,z) = PolynomialRing(GF(1618453), ["x", "y", "z"])

F = [84500*x^3*y^2+409500*x^3*y*z-134000*x^3*z^2+92950*x^2*y^3-717600*x^2*y^2*z+649050*x^2*y*z^2-67300*x^2*z^3-13520*x*y^4-1299610*x*y^3*z-352270*x*y^2*z^2+152490*x*y*z^3-8450*x*z^4-27040*y^5-370760*y^4*z-249380*y^3*z^2+9920*y^2*z^3+3900*y*z^4+1618500*x^2*y^2-1364300*x^2*y*z+132200*x^2*z^2+1320020*x*y^3+3352560*x*y^2*z-897700*x*y*z^2+33200*x*z^3+20176*y^4+1489456*y^3*z+526944*y^2*z^2-91520*y*z^3-4478760*x*y^2+1177760*x*y*z-32600*x*z^2-1517264*y^3-2514912*y^2*z+318320*y*z^2+2836544*y^2-301760*y*z,-6750*x^3*y^2+83175*x^3*y*z-244325*x^3*z^2-26550*x^2*y^3+131640*x^2*y^2*z+63815*x^2*y*z^2-100575*x^2*z^3-29520*x*y^4+97605*x*y^3*z-138395*x*y^2*z^2-83820*x*y*z^3-10350*x*z^4-10080*y^5+36420*y^4*z+13505*y^3*z^2-46845*y^2*z^3-19350*y*z^4+288930*x^2*y^2-1556620*x^2*y*z+203325*x^2*z^2+368934*x*y^3-140636*x*y^2*z-554790*x*y*z^2+41850*x*z^3+110232*y^4-276900*y^3*z-100287*y^2*z^2-7110*y*z^3-1861500*x*y^2+1451820*x*y*z-42300*x*z^2-328572*y^3-203352*y^2*z+261360*y*z^2+1188180*y^2-339480*y*z,19500*x^3*y^2+6250*x^3*y*z-485750*x^3*z^2+21450*x^2*y^3-208525*x^2*y^2*z+1194250*x^2*y*z^2-223025*x^2*z^3-3120*x*y^4-269545*x*y^3*z+590130*x*y^2*z^2+300755*x*y*z^3-25350*x*z^4-6240*y^5-78980*y^4*z+35950*y^3*z^2+106590*y^2*z^3+11700*y*z^4+265200*x^2*y^2-2654950*x^2*y*z+437350*x^2*z^2+272130*x*y^3+1890970*x*y^2*z-2282160*x*y*z^2+99600*x*z^3+47976*y^4+904464*y^3*z-206512*y^2*z^2-274560*y*z^3-3264540*x*y^2+3333460*x*y*z-97800*x*z^2-304152*y^3-1608712*y^2*z+954960*y*z^2+3168480*y^2-905280*y*z,-29250*x^3*y^2+228050*x^3*y*z-67400*x^3*z^2-115050*x^2*y^3+130990*x^2*y^2*z+169570*x^2*y*z^2-30650*x^2*z^3-127920*x*y^4+98540*x*y^3*z+45880*x*y^2*z^2+90*x*y*z^3-3450*x*z^4-43680*y^5+111760*y^4*z+153430*y^3*z^2+26740*y^2*z^3-6450*y*z^4+1089580*x^2*y^2-735170*x^2*y*z+61900*x^2*z^2+1089704*x*y^3+658442*x*y^2*z-259210*x*y*z^2+13950*x*z^3+174432*y^4-41776*y^3*z-9266*y^2*z^2-2370*y*z^3-2250068*x*y^2+519980*x*y*z-14100*x*z^2-761016*y^3-619512*y^2*z+87120*y*z^2+1063704*y^2-113160*y*z,29250*x^3*y^2-113050*x^3*y*z-217800*x^3*z^2+85800*x^2*y^3-195265*x^2*y^2*z+501390*x^2*y*z^2-119995*x^2*z^3+81120*x*y^4-252285*x*y^3*z+392990*x*y^2*z^2+168915*x*y*z^3-16930*x*z^4+24960*y^5-134740*y^4*z-46540*y^3*z^2+68560*y^2*z^3+6300*y*z^4-516080*x^2*y^2-797290*x^2*y*z+203790*x^2*z^2-511894*x*y^3+524534*x*y^2*z-1072472*x*y*z^2+54320*x*z^3-79224*y^4+644008*y^3*z-151216*y^2*z^2-148588*y*z^3-290756*x*y^2+1353444*x*y*z-40920*x*z^2+53280*y^3-545568*y^2*z+497312*y*z^2+1054848*y^2-450672*y*z,115050*x^3*y^2+610500*x^3*y*z+90450*x^3*z^2-14235*x^2*y^3-1752685*x^2*y^2*z-130335*x^2*y*z^2+49615*x^2*z^3-60645*x*y^4+19845*x*y^3*z-79265*x*y^2*z^2-92495*x*y*z^3+6760*x*z^4+19500*y^5+260170*y^4*z+85140*y^3*z^2-20650*y^2*z^3-3120*y*z^4+2268630*x^2*y^2-453480*x^2*y*z-64110*x^2*z^2-1083522*x*y^3+2686042*x*y^2*z+279754*x*y*z^2-18110*x*z^3+61260*y^4-89688*y^3*z-63232*y^2*z^2+69316*y*z^3-4759416*x*y^2-233436*x*y*z+9780*x*z^2+1174656*y^3-1047880*y^2*z-170936*y*z^2+2353728*y^2+90528*y*z,-39825*x^3*y^2+292170*x^3*y*z+45495*x^3*z^2-107910*x^2*y^3-221235*x^2*y^2*z+18470*x^2*y*z^2+22795*x^2*z^3-21465*x*y^4+268920*x*y^3*z+126075*x*y^2*z^2+7950*x*y*z^3+2760*x*z^4+31500*y^5-92235*y^4*z-74260*y^3*z^2-365*y^2*z^3+5160*y*z^4+1461012*x^2*y^2-168783*x^2*y*z-29145*x^2*z^2-331734*x*y^3+285418*x*y^2*z+66542*x*y*z^2-7710*x*z^3-3330*y^4-334311*y^3*z-127185*y^2*z^2+8346*y*z^3-2258202*x*y^2-91122*x*y*z+4230*x*z^2+281142*y^3-147534*y^2*z-54426*y*z^2+882648*y^2+33948*y*z,91140*x^3*y^2-551090*x^3*y*z+534470*x^3*z^2+141552*x^2*y^3-949962*x^2*y^2*z+2247966*x^2*y*z^2+595460*x^2*z^3+64362*x*y^4-344569*x*y^3*z-558297*x*y^2*z^2+490449*x*y*z^3+196455*x*z^4+7560*y^5+95199*y^4*z-50903*y^3*z^2-140969*y^2*z^3+2583*y*z^4+19890*z^5-1452960*x^2*y^2+5020450*x^2*y*z-825520*x^2*z^2-1215534*x*y^3+4830143*x*y^2*z-1497048*x*y*z^2-547095*x*z^3-132606*y^4-479343*y^3*z+180046*y^2*z^2-286407*y*z^3-85590*z^4+6479040*x*y^2-6267810*x*y*z+350130*x*z^2+1200834*y^3-3394386*y^2*z-250740*y*z^2+112320*z^3-5419260*y^2+1693260*y*z-41400*z^2,394940*x^3*y^2-600700*x^3*y*z+147440*x^3*z^2+613392*x^2*y^3-2437228*x^2*y^2*z-31872*x^2*y*z^2+170620*x^2*z^3+278902*x*y^4-1056890*x*y^3*z-1540414*x*y^2*z^2-134358*x*y*z^3+59960*x*z^4+32760*y^5+447074*y^4*z+268060*y^3*z^2-100328*y^2*z^3-42676*y*z^4+6630*z^5-4102724*x^2*y^2+2382208*x^2*y*z-240440*x^2*z^2-3615378*x*y^3+3828432*x*y^2*z+468698*x*y*z^2-169640*x*z^3-347196*y^4+511722*y^3*z+1103606*y^2*z^2+83038*y*z^3-28530*z^4+8461988*x*y^2-2448844*x*y*z+110960*x*z^2+3204396*y^3-1148264*y^2*z-309076*y*z^2+37440*z^3-4851528*y^2+645840*y*z-13800*z^2,245440*x^3*y^2-218440*x^3*y*z+118920*x^3*z^2+388362*x^2*y^3-1589246*x^2*y^2*z+4270*x^2*y*z^2-15002*x^2*z^3+182858*x*y^4-767384*x*y^3*z-1087960*x*y^2*z^2+126912*x*y*z^3-17690*x*z^4+23400*y^5+317110*y^4*z+162978*y^3*z^2-62854*y^2*z^3+2790*y*z^4-1248*z^5-2531692*x^2*y^2+2413552*x^2*y*z-275676*x^2*z^2-2290656*x*y^3+2964612*x*y^2*z+875096*x*y*z^2+35908*x*z^3-263724*y^4-62496*y^3*z+692408*y^2*z^2-92240*y*z^3+23940*z^4+5231128*x*y^2-4239208*x*y*z+167904*x*z^2+2063160*y^3-820456*y^2*z-668000*y*z^2-14304*z^3-3013536*y^2+1952976*y*z-57168*z^2,537726*x^3*y^2-570396*x^3*y*z-99522*x^3*z^2+177126*x^2*y^3-2641708*x^2*y^2*z-951610*x^2*y*z^2-119776*x^2*z^3-115845*x*y^4+1938056*x*y^3*z+689138*x*y^2*z^2-188616*x*y*z^3-44653*x*z^4-23625*y^5-313680*y^4*z-79142*y^3*z^2+79944*y^2*z^3+12527*y*z^4-5304*z^5-5282310*x^2*y^2+561042*x^2*y*z+134652*x^2*z^2+1190409*x*y^3+5109329*x*y^2*z+979457*x*y*z^2+94637*x*z^3+158535*y^4-1641783*y^3*z-422849*y^2*z^2+188063*y*z^3+16194*z^4+8805558*x*y^2+87420*x*y*z-43638*x*z^2-1503486*y^3-2545290*y^2*z-103686*y*z^2-14682*z^3-4025736*y^2-47196*y*z+4140*z^2,51750*x^3*y^2-249090*x^3*y*z+299460*x^3*z^2+87810*x^2*y^3-622808*x^2*y^2*z+1256768*x^2*y*z^2+278606*x^2*z^3+46578*x*y^4-283939*x*y^3*z-122385*x*y^2*z^2+394487*x*y*z^3+100795*x*z^4+7560*y^5+62439*y^4*z-69311*y^3*z^2-105573*y^2*z^3+1951*y*z^4+12774*z^5-782298*x^2*y^2+3033480*x^2*y*z-513192*x^2*z^2-773088*x*y^3+3006255*x*y^2*z-862598*x*y*z^2-253931*x*z^3-154854*y^4-106929*y^3*z+3408*y^2*z^2-264695*y*z^3-37758*z^4+3363228*x*y^2-4510470*x*y*z+236202*x*z^2+1113174*y^3-1899918*y^2*z-148908*y*z^2+45444*z^3-2934252*y^2+1551420*y*z-42048*z^2,1147250*x^4*y+5912750*x^4*z+725725*x^3*y^2-12377100*x^3*y*z+4432725*x^3*z^2-773435*x^2*y^3-13169390*x^2*y^2*z-8309335*x^2*y*z^2+1150610*x^2*z^3-281320*x*y^4+3301810*x*y^3*z-1796420*x*y^2*z^2-1569360*x*y*z^3+103090*x*z^4+171600*y^5+2310920*y^4*z+1016800*y^3*z^2-325540*y^2*z^3-47580*y*z^4+21939450*x^3*y-11607050*x^3*z+6724220*x^2*y^2+46484590*x^2*y*z-5636510*x^2*z^2-8363972*x*y^3+13236406*x*y^2*z+15249276*x*y*z^2-704170*x*z^3+238320*y^4-4569448*y^3*z+147444*y^2*z^2+1254604*y*z^3-61064460*x^2*y+6619580*x^2*z-10891580*x*y^2-48702436*x*y*z+1573000*x*z^2+9833616*y^3-557168*y^2*z-7123312*y*z^2+48799448*x*y-1154040*x*z+3063600*y^2+14950000*y*z-10682304*y,-397125*x^4*y+2974025*x^4*z-1376400*x^3*y^2-2705*x^3*y*z+2088355*x^3*z^2-1006635*x^2*y^3+395585*x^2*y^2*z+527470*x^2*y*z^2+508480*x^2*z^3+218760*x*y^4+869575*x*y^3*z+1332655*x*y^2*z^2+431370*x*y*z^3+42090*x*z^4+277200*y^5-777060*y^4*z-784340*y^3*z^2+12010*y^2*z^3+78690*y*z^4+14805190*x^3*y-5635435*x^3*z+8234972*x^2*y^2+10297778*x^2*y*z-2525690*x^2*z^2-3531294*x*y^3-2635499*x*y^2*z+1000808*x*y*z^2-292320*x*z^3-515160*y^4-1255836*y^3*z-1173938*y^2*z^2-199416*y*z^3-31139606*x^2*y+3030210*x^2*z-7952790*x*y^2-13930894*x*y*z+665850*x*z^2+3238632*y^3+1371960*y^2*z-1146762*y*z^2+20448396*x*y-499140*x*z+1872072*y^2+4464600*y*z-4005864*y,2218800*x^4*y-10724200*x^4*z+3167880*x^3*y^2-17158400*x^3*y*z+44242970*x^3*z^2-1551738*x^2*y^3-233237*x^2*y^2*z+20370606*x^2*y*z^2+36349185*x^2*z^3-4021008*x*y^4+16860851*x*y^3*z-50662837*x*y^2*z^2+1449919*x*y*z^3+9473205*x*z^4-1510560*y^5+9245484*y^4*z-1257223*y^3*z^2-11698924*y^2*z^3-669447*y*z^4+815490*z^5-21832140*x^3*y+34890210*x^3*z+6862098*x^2*y^2-19758547*x^2*y*z-73387265*x^2*z^2+40390938*x*y^3+13405147*x*y^2*z-10968426*x*y*z^2-40533855*x*z^3+16742952*y^4-77397960*y^3*z+11704985*y^2*z^2+2815737*y*z^3-5140170*z^4+40770600*x^2*y+3509290*x^2*z-165545874*x*y^2+7032746*x*y*z+50610120*x*z^2-39898548*y^3-15522684*y^2*z-4477506*y*z^2+11623500*z^3+25029660*x*y-14870460*x*z+80545140*y^2+8988540*y*z-10907640*z^2-11881800*y+3394800*z,9614800*x^4*y-2958400*x^4*z+13727480*x^3*y^2-38926980*x^3*y*z+12077440*x^3*z^2-6724198*x^2*y^3-48202508*x^2*y^2*z-37743902*x^2*y*z^2+10579820*x^2*z^3-17424368*x*y^4+26288240*x*y^3*z-38510274*x*y^2*z^2-14617848*x*y*z^3+2931210*x*z^4-6545760*y^5+33161344*y^4*z+26082350*y^3*z^2-4389358*y^2*z^3-2008166*y*z^4+271830*z^5-41206820*x^3*y+9879920*x^3*z+63256774*x^2*y^2+73485182*x^2*y*z-20987580*x^2*z^2+110865424*x*y^3+126633280*x*y^2*z+60504414*x*y*z^2-12536510*x*z^3+27110112*y^4-46868664*y^3*z+19076830*y^2*z^2+11827400*y*z^3-1713390*z^4+25039604*x^2*y+243880*x^2*z-196264120*x*y^2-75718300*x*y*z+15590840*x*z^2-66833352*y^3-58607776*y^2*z-25375412*y*z^2+3874500*z^3+28243328*x*y-4485320*x*z+76775736*y^2+24825072*y*z-3635880*z^2-10637040*y+1131600*z,6624800*x^4*y+4456800*x^4*z+9428380*x^3*y^2-32123880*x^3*y*z+13889140*x^3*z^2-4303208*x^2*y^3-45476486*x^2*y^2*z-32385320*x^2*y*z^2+3087198*x^2*z^3-11420032*x*y^4+17830726*x*y^3*z-31601150*x*y^2*z^2-2195978*x*y*z^3-294190*x*z^4-4268160*y^5+25096600*y^4*z+17577878*y^3*z^2-3261404*y^2*z^3-77010*y*z^4-51168*z^5-17855680*x^3*y-7898280*x^3*z+46018856*x^2*y^2+130710864*x^2*y*z-14697912*x^2*z^2+68337620*x*y^3+121570128*x*y^2*z+60966800*x*y*z^2+1627348*x*z^3+16075920*y^4-50526584*y^3*z+12307644*y^2*z^2+295640*y*z^3+1083876*z^4-116812448*x^2*y+16999032*x^2*z-168966056*x*y^2-256357336*x*y*z+3887048*x*z^2-329064*y^3-38129632*y^2*z-30943256*y*z^2-2549544*z^3+286261696*x*y-11929968*x*z+53058480*y^2+133675520*y*z-1170960*z^2-144710976*y+4687776*z,1035000*x^4*y-2566800*x^4*z+1092450*x^3*y^2-9976750*x^3*y*z+26275730*x^3*z^2-1571280*x^2*y^3-3648703*x^2*y^2*z+14898478*x^2*y*z^2+19447161*x^2*z^3-2491872*x*y^4+10455011*x*y^3*z-24472395*x*y^2*z^2+6015037*x*y*z^3+5255985*x*z^4-852480*y^5+6642444*y^4*z-4430001*y^3*z^2-9241278*y^2*z^3-20959*y*z^4+523734*z^5-1206210*x^3*y+11993940*x^3*z+17592132*x^2*y^2+5834381*x^2*y*z-39250039*x^2*z^2+25674570*x*y^3-4269971*x*y^2*z-18022208*x*y*z^2-19874311*x*z^3+8663112*y^4-45928152*y^3*z+2752721*y^2*z^2-2587003*y*z^3-2595546*z^4-60994644*x^2*y+9592434*x^2*z-124995966*x*y^2-44707334*x*y*z+25116044*x*z^2-16041132*y^3+9178620*y^2*z+2996442*y*z^2+4959360*z^3+141802404*x*y-12782724*x*z+55929780*y^2+33633948*y*z-5450376*z^2-58222296*y+3447936*z,5362070*x^4*y-6505790*x^4*z+5821626*x^3*y^2-28696478*x^3*y*z-9138468*x^3*z^2-106049*x^2*y^3+1281395*x^2*y^2*z-14985667*x^2*y*z^2-4555919*x^2*z^3-1325175*x*y^4+13077951*x*y^3*z+10026001*x*y^2*z^2-1493895*x*y*z^3-990082*x*z^4-207900*y^5-2786340*y^4*z-1018942*y^3*z^2+902698*y^2*z^3+172970*y*z^4-80886*z^5-55865018*x^3*y+16962236*x^3*z-27452463*x^2*y^2+45295614*x^2*y*z+17273351*x^2*z^2+14989059*x*y^3+796418*x*y^2*z+19062671*x*y*z^2+5576692*x*z^3+1759500*y^4-9635658*y^3*z-7072472*y^2*z^2+1395982*y*z^3+582768*z^4+118493090*x^2*y-14689346*x^2*z+29851896*x*y^2-10448386*x*y*z-9445198*x*z^2-16210836*y^3-3976614*y^2*z-5247580*y*z^2-1466730*z^3-86483964*x*y+4749084*x*z-7534548*y^2-5412012*y*z+1493736*z^2+18270648*y-488520*z,13090920*x^4*y+1996920*x^4*z+2670756*x^3*y^2-56719166*x^3*y*z-8059822*x^3*z^2-19211559*x^2*y^3-8173053*x^2*y^2*z-31244405*x^2*y*z^2-7541911*x^2*z^3-4475355*x*y^4+75185846*x*y^3*z+31241318*x*y^2*z^2-2116636*x*y*z^3-2209053*x*z^4+4720500*y^5-25658595*y^4*z-8983147*y^3*z^2+4340979*y^2*z^3+720367*y*z^4-217464*z^5-48710946*x^3*y-6114246*x^3*z+136257801*x^2*y^2+146571000*x^2*y*z+11500899*x^2*z^2-14266827*x*y^3+7433047*x*y^2*z+52326427*x*y*z^2+7600453*x*z^3-1198710*y^4-66572337*y^3*z-16779718*y^2*z^2+3003091*y*z^3+1098882*z^4+13097046*x^2*y-1739754*x^2*z-171003096*x*y^2-104842138*x*y*z-7535342*x*z^2+5365062*y^3-1381326*y^2*z-19363458*y*z^2-1929870*z^3+27347196*x*y+2194296*x*z+54581292*y^2+25247256*y*z+1373664*z^2-8826480*y-339480*z,3036000*x^4*y-7529280*x^4*z+4754460*x^3*y^2-21886456*x^3*y*z-6125988*x^3*z^2+1083858*x^2*y^3+2882442*x^2*y^2*z-16238698*x^2*y*z^2-11096786*x^2*z^3-1238286*x*y^4+11225644*x*y^3*z+1209768*x*y^2*z^2+11358052*x*y*z^3-4233002*x*z^4-493560*y^5-1136814*y^4*z-1771102*y^3*z^2+448850*y^2*z^3+2065542*y*z^4-408084*z^5-55501776*x^3*y+24113616*x^3*z-55614846*x^2*y^2+94986016*x^2*y*z-8598546*x^2*z^2+6469710*x*y^3+1278090*x*y^2*z+83999142*x*y*z^2+5724082*x*z^3+12653748*y^4-34027290*y^3*z-6002820*y^2*z^2-3495746*y*z^3+2306412*z^4+305848404*x^2*y-34761444*x^2*z+138271764*x*y^2-78335080*x*y*z+16483548*x*z^2-71935092*y^3-256656*y^2*z-52845548*y*z^2+2134032*z^3-498731712*x*y+19626192*x*z-38576448*y^2+18346248*y*z-6573024*z^2+236207952*y-7312032*z,130539400*x^5+125359940*x^4*y-500615010*x^4*z-178410619*x^3*y^2-453828508*x^3*y*z-597757493*x^3*z^2-193896509*x^2*y^3+655467845*x^2*y^2*z-115189617*x^2*y*z^2-248963509*x^2*z^3+21706440*x*y^4+282747911*x*y^3*z+480739706*x*y^2*z^2+35165475*x*y*z^3-46362132*x*z^4+41540400*y^5-220609380*y^4*z-111665192*y^3*z^2+53929838*y^2*z^3+10244860*y*z^4-3316326*z^5-563421530*x^4+1013636161*x^3*y+1342377737*x^3*z+1043111293*x^2*y^2+1604287170*x^2*y*z+1219076949*x^2*z^2-206906982*x*y^3-1084530057*x*y^2*z+217399523*x*y*z^2+334677496*x*z^3-83357640*y^4-151364532*y^3*z-306767878*y^2*z^2-26163010*y*z^3+30526140*z^4+403568498*x^3-2533406722*x^2*y-1556408958*x^2*z-749648550*x*y^2-1340906908*x*y*z-833065132*x*z^2+172582632*y^3+327759456*y^2*z-83423594*y*z^2-107922906*z^3+240713192*x^2+1550883924*x*y+811372600*x*z+148110696*y^2+329138016*y*z+181515036*z^2-226110528*x-279195336*y-142515672*z+40058640];

id = ideal(P,F);
tim = @elapsed gen_fglm(id, target_order = :degrevlex)
println("time $(tim)")
exit()

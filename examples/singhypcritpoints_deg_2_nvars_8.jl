using genFGLM
P, (x1, x2, x3, x4, x5, x6, x7, x8)  = PolynomialRing(GF(1767691), ["x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8"]);
F = [29268340*x1^4-43194292*x1^3*x2-11397064*x1^3*x3-107237916*x1^3*x4+28333536*x1^3*x5+36560412*x1^3*x6-13098600*x1^3*x7+36807028*x1^3*x8+53940402*x1^2*x2^2-29991014*x1^2*x2*x3+75944978*x1^2*x2*x4-33202050*x1^2*x2*x5-19556350*x1^2*x2*x6+25172512*x1^2*x2*x7-32979550*x1^2*x2*x8+3149664*x1^2*x3^2+57288346*x1^2*x3*x4+24035520*x1^2*x3*x5+62769566*x1^2*x3*x6-31722484*x1^2*x3*x7+28819382*x1^2*x3*x8+137167688*x1^2*x4^2-77835602*x1^2*x4*x5-72338396*x1^2*x4*x6+36508884*x1^2*x4*x7-105952764*x1^2*x4*x8+62914860*x1^2*x5^2+41353090*x1^2*x5*x6+8123308*x1^2*x5*x7-29449182*x1^2*x5*x8-32961484*x1^2*x6^2+34425500*x1^2*x6*x7+2677416*x1^2*x6*x8-33987424*x1^2*x7^2+25048172*x1^2*x7*x8-11062576*x1^2*x8^2-30977790*x1*x2^3-8094536*x1*x2^2*x3-71038404*x1*x2^2*x4+57586734*x1*x2^2*x5+3127784*x1*x2^2*x6-21384966*x1*x2^2*x7+53575218*x1*x2^2*x8+27626476*x1*x2*x3^2+62594460*x1*x2*x3*x4-45928662*x1*x2*x3*x5-113324492*x1*x2*x3*x6+28041300*x1*x2*x3*x7-13455414*x1*x2*x3*x8-21244114*x1*x2*x4^2+22180798*x1*x2*x4*x5-33492400*x1*x2*x4*x6+39313344*x1*x2*x4*x7+49874050*x1*x2*x4*x8-65206974*x1*x2*x5^2+31673722*x1*x2*x5*x6-5346728*x1*x2*x5*x7-32205300*x1*x2*x5*x8+15015194*x1*x2*x6^2-62598140*x1*x2*x6*x7+68945798*x1*x2*x6*x8+73144268*x1*x2*x7^2+3573988*x1*x2*x7*x8-7934700*x1*x2*x8^2-27206128*x1*x3^3-95164652*x1*x3^2*x4+20941248*x1*x3^2*x5-56155588*x1*x3^2*x6-45580360*x1*x3^2*x7+19628084*x1*x3^2*x8-114237700*x1*x3*x4^2+83526778*x1*x3*x4*x5-159563264*x1*x3*x4*x6-39334548*x1*x3*x4*x7+59050526*x1*x3*x4*x8-49194288*x1*x3*x5^2+29576422*x1*x3*x5*x6+15601540*x1*x3*x5*x7+25070814*x1*x3*x5*x8+126794612*x1*x3*x6^2-88861828*x1*x3*x6*x7+124259938*x1*x3*x6*x8-6439504*x1*x3*x7^2+37562112*x1*x3*x7*x8+12261414*x1*x3*x8^2-75113388*x1*x4^3+102461856*x1*x4^2*x5+9000036*x1*x4^2*x6-57929634*x1*x4^2*x7+129352852*x1*x4^2*x8-171010374*x1*x4*x5^2-55653048*x1*x4*x5*x6-34156980*x1*x4*x5*x7-12432286*x1*x4*x5*x8+104604580*x1*x4*x6^2-51961704*x1*x4*x6*x7+40888892*x1*x4*x6*x8+156510900*x1*x4*x7^2-31338420*x1*x4*x7*x8-9285648*x1*x4*x8^2+61333848*x1*x5^3+92622030*x1*x5^2*x6-33365940*x1*x5^2*x7+31154022*x1*x5^2*x8-13526520*x1*x5*x6^2+13405428*x1*x5*x6*x7-67090666*x1*x5*x6*x8-58239336*x1*x5*x7^2+23248616*x1*x5*x7*x8-37416978*x1*x5*x8^2-54391708*x1*x6^3+55462010*x1*x6^2*x7-45771160*x1*x6^2*x8-37708764*x1*x6*x7^2+84922720*x1*x6*x7*x8-45935220*x1*x6*x8^2+49559328*x1*x7^3-56251388*x1*x7^2*x8+36328006*x1*x7*x8^2-17472112*x1*x8^3+9599826*x2^4+1523674*x2^3*x3+18769332*x2^3*x4-18685740*x2^3*x5-12659744*x2^3*x6+24595552*x2^3*x7-6697594*x2^3*x8+11327214*x2^2*x3^2+2456360*x2^2*x3*x4-30890092*x2^2*x3*x5+81504806*x2^2*x3*x6-30214454*x2^2*x3*x7-22459658*x2^2*x3*x8+7115662*x2^2*x4^2-43558866*x2^2*x4*x5+41147872*x2^2*x4*x6+1250468*x2^2*x4*x7-48466230*x2^2*x4*x8+61116778*x2^2*x5^2-18529238*x2^2*x5*x6-10831546*x2^2*x5*x7+38119706*x2^2*x5*x8-11649360*x2^2*x6^2+6212752*x2^2*x6*x7-55909420*x2^2*x6*x8-1207890*x2^2*x7^2+25139500*x2^2*x7*x8+27990826*x2^2*x8^2+5175524*x2*x3^3+28520214*x2*x3^2*x4+3233844*x2*x3^2*x5-1446950*x2*x3^2*x6+54803892*x2*x3^2*x7-58234792*x2*x3^2*x8+16594080*x2*x3*x4^2-16384988*x2*x3*x4*x5+130596894*x2*x3*x4*x6-77331200*x2*x3*x4*x7-116550384*x2*x3*x4*x8-661146*x2*x3*x5^2-36769086*x2*x3*x5*x6-43653614*x2*x3*x5*x7+85169574*x2*x3*x5*x8-84644170*x2*x3*x6^2+154043322*x2*x3*x6*x7-70569506*x2*x3*x6*x8-46129998*x2*x3*x7^2-27791686*x2*x3*x7*x8+95676066*x2*x3*x8^2+2561204*x2*x4^3-18744170*x2*x4^2*x5+82164322*x2*x4^2*x6-116959328*x2*x4^2*x7-75243320*x2*x4^2*x8+64329396*x2*x4*x5^2-73807856*x2*x4*x5*x6+94091286*x2*x4*x5*x7+105723362*x2*x4*x5*x8-37577228*x2*x4*x6^2+42828662*x2*x4*x6*x7-110139308*x2*x4*x6*x8-68452030*x2*x4*x7^2+115488998*x2*x4*x7*x8+65989918*x2*x4*x8^2-25971714*x2*x5^3-53090834*x2*x5^2*x6+84020838*x2*x5^2*x7-29676360*x2*x5^2*x8-11303846*x2*x5*x6^2-14481992*x2*x5*x6*x7+126277762*x2*x5*x6*x8+36260786*x2*x5*x7^2-36267268*x2*x5*x7*x8-88169622*x2*x5*x8^2+58567374*x2*x6^3-104254058*x2*x6^2*x7-8146384*x2*x6^2*x8+71893362*x2*x6*x7^2-76814952*x2*x6*x7*x8+46455444*x2*x6*x8^2-37662728*x2*x7^3+67352126*x2*x7^2*x8+4439946*x2*x7*x8^2-21377074*x2*x8^3+16123888*x3^4+67935316*x3^3*x4-44851440*x3^3*x5+18546908*x3^3*x6+47754296*x3^3*x7-23522612*x3^3*x8+123914916*x3^2*x4^2-131110580*x3^2*x4*x5-459520*x3^2*x4*x6+187700512*x3^2*x4*x7-163138810*x3^2*x4*x8+69231888*x3^2*x5^2-31044956*x3^2*x5*x6-97449272*x3^2*x5*x7+25133964*x3^2*x5*x8+9429756*x3^2*x6^2-42365744*x3^2*x6*x7+87590266*x3^2*x6*x8+76314480*x3^2*x7^2-152580876*x3^2*x7*x8+82222826*x3^2*x8^2+97780186*x3*x4^3-155000416*x3*x4^2*x5+23831050*x3*x4^2*x6+85836938*x3*x4^2*x7-214033028*x3*x4^2*x8+120737334*x3*x4*x5^2-15022962*x3*x4*x5*x6-188187942*x3*x4*x5*x7+195042506*x3*x4*x5*x8-77769782*x3*x4*x6^2+174762674*x3*x4*x6*x7-13187428*x3*x4*x6*x8-41405918*x3*x4*x7^2-75421250*x3*x4*x7*x8+136962932*x3*x4*x8^2-77355432*x3*x5^3+44518698*x3*x5^2*x6+58298124*x3*x5^2*x7+53460954*x3*x5^2*x8+98268042*x3*x5*x6^2-42193750*x3*x5*x6*x7-37290040*x3*x5*x6*x8-49741916*x3*x5*x7^2+139332338*x3*x5*x7*x8-124295778*x3*x5*x8^2-52937438*x3*x6^3+32682260*x3*x6^2*x7-38817348*x3*x6^2*x8-1859942*x3*x6*x7^2+59935044*x3*x6*x7*x8-15999944*x3*x6*x8^2+2122772*x3*x7^3-63704214*x3*x7^2*x8+104293580*x3*x7*x8^2-40086754*x3*x8^3+29601832*x4^4-66429548*x4^3*x5+9723358*x4^3*x6-25606524*x4^3*x7-94914624*x4^3*x8+93211078*x4^2*x5^2+5403312*x4^2*x5*x6+15340828*x4^2*x5*x7+146512338*x4^2*x5*x8-31755128*x4^2*x6^2+35707034*x4^2*x6*x7-17874420*x4^2*x6*x8-37218796*x4^2*x7^2+24785990*x4^2*x7*x8+72544084*x4^2*x8^2-86100930*x4*x5^3-75553762*x4*x5^2*x6+170863262*x4*x5^2*x7-71723712*x4*x5^2*x8+29463020*x4*x5*x6^2+22470294*x4*x5*x6*x7+45028932*x4*x5*x6*x8+79504894*x4*x5*x7^2-104377586*x4*x5*x7*x8-82217878*x4*x5*x8^2+37342462*x4*x6^3-153439444*x4*x6^2*x7+15634820*x4*x6^2*x8+115369888*x4*x6*x7^2-67836692*x4*x6*x7*x8+30048650*x4*x6*x8^2-77404548*x4*x7^3+139622916*x4*x7^2*x8-30277116*x4*x7*x8^2-17361960*x4*x8^3+61286220*x5^4+67360842*x5^3*x6-63064044*x5^3*x7-46512846*x5^3*x8-52945432*x5^2*x6^2-9878674*x5^2*x6*x7-26193978*x5^2*x6*x8+18531328*x5^2*x7^2+6850266*x5^2*x7*x8+35159706*x5^2*x8^2-41170592*x5*x6^3+47158446*x5*x6^2*x7+49119746*x5*x6^2*x8-16315714*x5*x6*x7^2+3398884*x5*x6*x7*x8-31397374*x5*x6*x8^2+28824892*x5*x7^3-34981610*x5*x7^2*x8-31955062*x5*x7*x8^2+26519856*x5*x8^3+22700612*x6^4-13214778*x6^3*x7-9676152*x6^3*x8-15311328*x6^2*x7^2-2312926*x6^2*x7*x8+9576276*x6^2*x8^2+19727252*x6*x7^3-17882740*x6*x7^2*x8+16996030*x6*x7*x8^2-10756500*x6*x8^3-16419044*x7^4+33508028*x7^3*x8-15574708*x7^2*x8^2-2524790*x7*x8^3+1719664*x8^4+29556292*x1^3-57410462*x1^2*x2-58680314*x1^2*x3-60801932*x1^2*x4-9681046*x1^2*x5+63166192*x1^2*x6+12258148*x1^2*x7+4124432*x1^2*x8+50783600*x1*x2^2+48915598*x1*x2*x3+88127690*x1*x2*x4-24949948*x1*x2*x5-109977726*x1*x2*x6+71485992*x1*x2*x7+28406168*x1*x2*x8+50010892*x1*x3^2+47272050*x1*x3*x4-58476634*x1*x3*x5+38133494*x1*x3*x6-31129552*x1*x3*x7+75052760*x1*x3*x8-19272602*x1*x4^2+59900450*x1*x4*x5-67962796*x1*x4*x6+72235344*x1*x4*x7+70635188*x1*x4*x8+75286446*x1*x5^2-8945146*x1*x5*x6-27146488*x1*x5*x7-102657068*x1*x5*x8-23713474*x1*x6^2+62193460*x1*x6*x7-5178160*x1*x6*x8+3972388*x1*x7^2+61808112*x1*x7*x8-40976374*x1*x8^2-24446436*x2^3-9692844*x2^2*x3-26829922*x2^2*x4-7437462*x2^2*x5+75291686*x2^2*x6-63242774*x2^2*x7-30387896*x2^2*x8-18921114*x2*x3^2-10769504*x2*x3*x4+80816408*x2*x3*x5-55050296*x2*x3*x6-24864044*x2*x3*x7-100953048*x2*x3*x8+4253692*x2*x4^2+29942696*x2*x4*x5+42072966*x2*x4*x6-149608656*x2*x4*x7-64014352*x2*x4*x8-98037276*x2*x5^2+16165674*x2*x5*x6+20512054*x2*x5*x7+39860986*x2*x5*x8+3190070*x2*x6^2+20369418*x2*x6*x7+35288154*x2*x6*x8-25632226*x2*x7^2-16662286*x2*x7*x8+41992962*x2*x8^2-15255588*x3^3-8461172*x3^2*x4+30454868*x3^2*x5-39062468*x3^2*x6+17120536*x3^2*x7-48907266*x3^2*x8+31597934*x3*x4^2+37914508*x3*x4*x5-65285262*x3*x4*x6-37433952*x3*x4*x7-102869128*x3*x4*x8-51613518*x3*x5^2-85630234*x3*x5*x6+63766310*x3*x5*x7-11223230*x3*x5*x8+116229868*x3*x6^2-83491306*x3*x6*x7+119359454*x3*x6*x8-4988114*x3*x7^2-51789322*x3*x7*x8+50400552*x3*x8^2+33023278*x4^3-28638824*x4^2*x5-27321594*x4^2*x6-27738530*x4^2*x7-73965966*x4^2*x8-39124148*x4*x5^2+32091662*x4*x5*x6-54155612*x4*x5*x7+63982956*x4*x5*x8+24233026*x4*x6^2+39005196*x4*x6*x7+67995312*x4*x6*x8-11818880*x4*x7^2-34077056*x4*x7*x8+53484122*x4*x8^2-35445942*x5^3+32286418*x5^2*x6-18092102*x5^2*x7+75288504*x5^2*x8+61209842*x5*x6^2-5907198*x5*x6*x7-94427370*x5*x6*x8+13663378*x5*x7^2-19020562*x5*x7*x8-14053526*x5*x8^2-56488798*x6^3+41573594*x6^2*x7-24725498*x6^2*x8-12399376*x6*x7^2+71346700*x6*x7*x8-38996698*x6*x8^2-4468388*x7^3-4815740*x7^2*x8+23225414*x7*x8^2-12178746*x8^3+78174240*x1^2-91174444*x1*x2-86304094*x1*x3-133971964*x1*x4-7117850*x1*x5+113805140*x1*x6-27299686*x1*x7+51416068*x1*x8+48094708*x2^2+34140014*x2*x3+54311846*x2*x4+37469112*x2*x5-106242782*x2*x6+49921888*x2*x7+3555814*x2*x8+32742992*x3^2+47427892*x3*x4-9159396*x3*x5+1121510*x3*x6-9248326*x3*x7+30861670*x3*x8+33978168*x4^2-10091278*x4*x5-70893390*x4*x6+102910436*x4*x7-15378600*x4*x8+70100830*x5^2-2277460*x5*x6-19686100*x5*x7-55489884*x5*x8-7106272*x6^2+2761390*x6*x7+28200396*x6*x8+10303188*x7^2+10518710*x7*x8-10224836*x8^2+47424106*x1-43661118*x2-30536004*x3-26253626*x4-29415094*x5+44525986*x6-4042790*x7+13316022*x8+16535152, -43194292*x1^3+107880804*x1^2*x2-29991014*x1^2*x3+75944978*x1^2*x4-33202050*x1^2*x5-19556350*x1^2*x6+25172512*x1^2*x7-32979550*x1^2*x8-92933370*x1*x2^2-16189072*x1*x2*x3-142076808*x1*x2*x4+115173468*x1*x2*x5+6255568*x1*x2*x6-42769932*x1*x2*x7+107150436*x1*x2*x8+27626476*x1*x3^2+62594460*x1*x3*x4-45928662*x1*x3*x5-113324492*x1*x3*x6+28041300*x1*x3*x7-13455414*x1*x3*x8-21244114*x1*x4^2+22180798*x1*x4*x5-33492400*x1*x4*x6+39313344*x1*x4*x7+49874050*x1*x4*x8-65206974*x1*x5^2+31673722*x1*x5*x6-5346728*x1*x5*x7-32205300*x1*x5*x8+15015194*x1*x6^2-62598140*x1*x6*x7+68945798*x1*x6*x8+73144268*x1*x7^2+3573988*x1*x7*x8-7934700*x1*x8^2+38399304*x2^3+4571022*x2^2*x3+56307996*x2^2*x4-56057220*x2^2*x5-37979232*x2^2*x6+73786656*x2^2*x7-20092782*x2^2*x8+22654428*x2*x3^2+4912720*x2*x3*x4-61780184*x2*x3*x5+163009612*x2*x3*x6-60428908*x2*x3*x7-44919316*x2*x3*x8+14231324*x2*x4^2-87117732*x2*x4*x5+82295744*x2*x4*x6+2500936*x2*x4*x7-96932460*x2*x4*x8+122233556*x2*x5^2-37058476*x2*x5*x6-21663092*x2*x5*x7+76239412*x2*x5*x8-23298720*x2*x6^2+12425504*x2*x6*x7-111818840*x2*x6*x8-2415780*x2*x7^2+50279000*x2*x7*x8+55981652*x2*x8^2+5175524*x3^3+28520214*x3^2*x4+3233844*x3^2*x5-1446950*x3^2*x6+54803892*x3^2*x7-58234792*x3^2*x8+16594080*x3*x4^2-16384988*x3*x4*x5+130596894*x3*x4*x6-77331200*x3*x4*x7-116550384*x3*x4*x8-661146*x3*x5^2-36769086*x3*x5*x6-43653614*x3*x5*x7+85169574*x3*x5*x8-84644170*x3*x6^2+154043322*x3*x6*x7-70569506*x3*x6*x8-46129998*x3*x7^2-27791686*x3*x7*x8+95676066*x3*x8^2+2561204*x4^3-18744170*x4^2*x5+82164322*x4^2*x6-116959328*x4^2*x7-75243320*x4^2*x8+64329396*x4*x5^2-73807856*x4*x5*x6+94091286*x4*x5*x7+105723362*x4*x5*x8-37577228*x4*x6^2+42828662*x4*x6*x7-110139308*x4*x6*x8-68452030*x4*x7^2+115488998*x4*x7*x8+65989918*x4*x8^2-25971714*x5^3-53090834*x5^2*x6+84020838*x5^2*x7-29676360*x5^2*x8-11303846*x5*x6^2-14481992*x5*x6*x7+126277762*x5*x6*x8+36260786*x5*x7^2-36267268*x5*x7*x8-88169622*x5*x8^2+58567374*x6^3-104254058*x6^2*x7-8146384*x6^2*x8+71893362*x6*x7^2-76814952*x6*x7*x8+46455444*x6*x8^2-37662728*x7^3+67352126*x7^2*x8+4439946*x7*x8^2-21377074*x8^3-57410462*x1^2+101567200*x1*x2+48915598*x1*x3+88127690*x1*x4-24949948*x1*x5-109977726*x1*x6+71485992*x1*x7+28406168*x1*x8-73339308*x2^2-19385688*x2*x3-53659844*x2*x4-14874924*x2*x5+150583372*x2*x6-126485548*x2*x7-60775792*x2*x8-18921114*x3^2-10769504*x3*x4+80816408*x3*x5-55050296*x3*x6-24864044*x3*x7-100953048*x3*x8+4253692*x4^2+29942696*x4*x5+42072966*x4*x6-149608656*x4*x7-64014352*x4*x8-98037276*x5^2+16165674*x5*x6+20512054*x5*x7+39860986*x5*x8+3190070*x6^2+20369418*x6*x7+35288154*x6*x8-25632226*x7^2-16662286*x7*x8+41992962*x8^2-91174444*x1+96189416*x2+34140014*x3+54311846*x4+37469112*x5-106242782*x6+49921888*x7+3555814*x8-43661118, -11397064*x1^3-29991014*x1^2*x2+6299328*x1^2*x3+57288346*x1^2*x4+24035520*x1^2*x5+62769566*x1^2*x6-31722484*x1^2*x7+28819382*x1^2*x8-8094536*x1*x2^2+55252952*x1*x2*x3+62594460*x1*x2*x4-45928662*x1*x2*x5-113324492*x1*x2*x6+28041300*x1*x2*x7-13455414*x1*x2*x8-81618384*x1*x3^2-190329304*x1*x3*x4+41882496*x1*x3*x5-112311176*x1*x3*x6-91160720*x1*x3*x7+39256168*x1*x3*x8-114237700*x1*x4^2+83526778*x1*x4*x5-159563264*x1*x4*x6-39334548*x1*x4*x7+59050526*x1*x4*x8-49194288*x1*x5^2+29576422*x1*x5*x6+15601540*x1*x5*x7+25070814*x1*x5*x8+126794612*x1*x6^2-88861828*x1*x6*x7+124259938*x1*x6*x8-6439504*x1*x7^2+37562112*x1*x7*x8+12261414*x1*x8^2+1523674*x2^3+22654428*x2^2*x3+2456360*x2^2*x4-30890092*x2^2*x5+81504806*x2^2*x6-30214454*x2^2*x7-22459658*x2^2*x8+15526572*x2*x3^2+57040428*x2*x3*x4+6467688*x2*x3*x5-2893900*x2*x3*x6+109607784*x2*x3*x7-116469584*x2*x3*x8+16594080*x2*x4^2-16384988*x2*x4*x5+130596894*x2*x4*x6-77331200*x2*x4*x7-116550384*x2*x4*x8-661146*x2*x5^2-36769086*x2*x5*x6-43653614*x2*x5*x7+85169574*x2*x5*x8-84644170*x2*x6^2+154043322*x2*x6*x7-70569506*x2*x6*x8-46129998*x2*x7^2-27791686*x2*x7*x8+95676066*x2*x8^2+64495552*x3^3+203805948*x3^2*x4-134554320*x3^2*x5+55640724*x3^2*x6+143262888*x3^2*x7-70567836*x3^2*x8+247829832*x3*x4^2-262221160*x3*x4*x5-919040*x3*x4*x6+375401024*x3*x4*x7-326277620*x3*x4*x8+138463776*x3*x5^2-62089912*x3*x5*x6-194898544*x3*x5*x7+50267928*x3*x5*x8+18859512*x3*x6^2-84731488*x3*x6*x7+175180532*x3*x6*x8+152628960*x3*x7^2-305161752*x3*x7*x8+164445652*x3*x8^2+97780186*x4^3-155000416*x4^2*x5+23831050*x4^2*x6+85836938*x4^2*x7-214033028*x4^2*x8+120737334*x4*x5^2-15022962*x4*x5*x6-188187942*x4*x5*x7+195042506*x4*x5*x8-77769782*x4*x6^2+174762674*x4*x6*x7-13187428*x4*x6*x8-41405918*x4*x7^2-75421250*x4*x7*x8+136962932*x4*x8^2-77355432*x5^3+44518698*x5^2*x6+58298124*x5^2*x7+53460954*x5^2*x8+98268042*x5*x6^2-42193750*x5*x6*x7-37290040*x5*x6*x8-49741916*x5*x7^2+139332338*x5*x7*x8-124295778*x5*x8^2-52937438*x6^3+32682260*x6^2*x7-38817348*x6^2*x8-1859942*x6*x7^2+59935044*x6*x7*x8-15999944*x6*x8^2+2122772*x7^3-63704214*x7^2*x8+104293580*x7*x8^2-40086754*x8^3-58680314*x1^2+48915598*x1*x2+100021784*x1*x3+47272050*x1*x4-58476634*x1*x5+38133494*x1*x6-31129552*x1*x7+75052760*x1*x8-9692844*x2^2-37842228*x2*x3-10769504*x2*x4+80816408*x2*x5-55050296*x2*x6-24864044*x2*x7-100953048*x2*x8-45766764*x3^2-16922344*x3*x4+60909736*x3*x5-78124936*x3*x6+34241072*x3*x7-97814532*x3*x8+31597934*x4^2+37914508*x4*x5-65285262*x4*x6-37433952*x4*x7-102869128*x4*x8-51613518*x5^2-85630234*x5*x6+63766310*x5*x7-11223230*x5*x8+116229868*x6^2-83491306*x6*x7+119359454*x6*x8-4988114*x7^2-51789322*x7*x8+50400552*x8^2-86304094*x1+34140014*x2+65485984*x3+47427892*x4-9159396*x5+1121510*x6-9248326*x7+30861670*x8-30536004, -107237916*x1^3+75944978*x1^2*x2+57288346*x1^2*x3+274335376*x1^2*x4-77835602*x1^2*x5-72338396*x1^2*x6+36508884*x1^2*x7-105952764*x1^2*x8-71038404*x1*x2^2+62594460*x1*x2*x3-42488228*x1*x2*x4+22180798*x1*x2*x5-33492400*x1*x2*x6+39313344*x1*x2*x7+49874050*x1*x2*x8-95164652*x1*x3^2-228475400*x1*x3*x4+83526778*x1*x3*x5-159563264*x1*x3*x6-39334548*x1*x3*x7+59050526*x1*x3*x8-225340164*x1*x4^2+204923712*x1*x4*x5+18000072*x1*x4*x6-115859268*x1*x4*x7+258705704*x1*x4*x8-171010374*x1*x5^2-55653048*x1*x5*x6-34156980*x1*x5*x7-12432286*x1*x5*x8+104604580*x1*x6^2-51961704*x1*x6*x7+40888892*x1*x6*x8+156510900*x1*x7^2-31338420*x1*x7*x8-9285648*x1*x8^2+18769332*x2^3+2456360*x2^2*x3+14231324*x2^2*x4-43558866*x2^2*x5+41147872*x2^2*x6+1250468*x2^2*x7-48466230*x2^2*x8+28520214*x2*x3^2+33188160*x2*x3*x4-16384988*x2*x3*x5+130596894*x2*x3*x6-77331200*x2*x3*x7-116550384*x2*x3*x8+7683612*x2*x4^2-37488340*x2*x4*x5+164328644*x2*x4*x6-233918656*x2*x4*x7-150486640*x2*x4*x8+64329396*x2*x5^2-73807856*x2*x5*x6+94091286*x2*x5*x7+105723362*x2*x5*x8-37577228*x2*x6^2+42828662*x2*x6*x7-110139308*x2*x6*x8-68452030*x2*x7^2+115488998*x2*x7*x8+65989918*x2*x8^2+67935316*x3^3+247829832*x3^2*x4-131110580*x3^2*x5-459520*x3^2*x6+187700512*x3^2*x7-163138810*x3^2*x8+293340558*x3*x4^2-310000832*x3*x4*x5+47662100*x3*x4*x6+171673876*x3*x4*x7-428066056*x3*x4*x8+120737334*x3*x5^2-15022962*x3*x5*x6-188187942*x3*x5*x7+195042506*x3*x5*x8-77769782*x3*x6^2+174762674*x3*x6*x7-13187428*x3*x6*x8-41405918*x3*x7^2-75421250*x3*x7*x8+136962932*x3*x8^2+118407328*x4^3-199288644*x4^2*x5+29170074*x4^2*x6-76819572*x4^2*x7-284743872*x4^2*x8+186422156*x4*x5^2+10806624*x4*x5*x6+30681656*x4*x5*x7+293024676*x4*x5*x8-63510256*x4*x6^2+71414068*x4*x6*x7-35748840*x4*x6*x8-74437592*x4*x7^2+49571980*x4*x7*x8+145088168*x4*x8^2-86100930*x5^3-75553762*x5^2*x6+170863262*x5^2*x7-71723712*x5^2*x8+29463020*x5*x6^2+22470294*x5*x6*x7+45028932*x5*x6*x8+79504894*x5*x7^2-104377586*x5*x7*x8-82217878*x5*x8^2+37342462*x6^3-153439444*x6^2*x7+15634820*x6^2*x8+115369888*x6*x7^2-67836692*x6*x7*x8+30048650*x6*x8^2-77404548*x7^3+139622916*x7^2*x8-30277116*x7*x8^2-17361960*x8^3-60801932*x1^2+88127690*x1*x2+47272050*x1*x3-38545204*x1*x4+59900450*x1*x5-67962796*x1*x6+72235344*x1*x7+70635188*x1*x8-26829922*x2^2-10769504*x2*x3+8507384*x2*x4+29942696*x2*x5+42072966*x2*x6-149608656*x2*x7-64014352*x2*x8-8461172*x3^2+63195868*x3*x4+37914508*x3*x5-65285262*x3*x6-37433952*x3*x7-102869128*x3*x8+99069834*x4^2-57277648*x4*x5-54643188*x4*x6-55477060*x4*x7-147931932*x4*x8-39124148*x5^2+32091662*x5*x6-54155612*x5*x7+63982956*x5*x8+24233026*x6^2+39005196*x6*x7+67995312*x6*x8-11818880*x7^2-34077056*x7*x8+53484122*x8^2-133971964*x1+54311846*x2+47427892*x3+67956336*x4-10091278*x5-70893390*x6+102910436*x7-15378600*x8-26253626, 28333536*x1^3-33202050*x1^2*x2+24035520*x1^2*x3-77835602*x1^2*x4+125829720*x1^2*x5+41353090*x1^2*x6+8123308*x1^2*x7-29449182*x1^2*x8+57586734*x1*x2^2-45928662*x1*x2*x3+22180798*x1*x2*x4-130413948*x1*x2*x5+31673722*x1*x2*x6-5346728*x1*x2*x7-32205300*x1*x2*x8+20941248*x1*x3^2+83526778*x1*x3*x4-98388576*x1*x3*x5+29576422*x1*x3*x6+15601540*x1*x3*x7+25070814*x1*x3*x8+102461856*x1*x4^2-342020748*x1*x4*x5-55653048*x1*x4*x6-34156980*x1*x4*x7-12432286*x1*x4*x8+184001544*x1*x5^2+185244060*x1*x5*x6-66731880*x1*x5*x7+62308044*x1*x5*x8-13526520*x1*x6^2+13405428*x1*x6*x7-67090666*x1*x6*x8-58239336*x1*x7^2+23248616*x1*x7*x8-37416978*x1*x8^2-18685740*x2^3-30890092*x2^2*x3-43558866*x2^2*x4+122233556*x2^2*x5-18529238*x2^2*x6-10831546*x2^2*x7+38119706*x2^2*x8+3233844*x2*x3^2-16384988*x2*x3*x4-1322292*x2*x3*x5-36769086*x2*x3*x6-43653614*x2*x3*x7+85169574*x2*x3*x8-18744170*x2*x4^2+128658792*x2*x4*x5-73807856*x2*x4*x6+94091286*x2*x4*x7+105723362*x2*x4*x8-77915142*x2*x5^2-106181668*x2*x5*x6+168041676*x2*x5*x7-59352720*x2*x5*x8-11303846*x2*x6^2-14481992*x2*x6*x7+126277762*x2*x6*x8+36260786*x2*x7^2-36267268*x2*x7*x8-88169622*x2*x8^2-44851440*x3^3-131110580*x3^2*x4+138463776*x3^2*x5-31044956*x3^2*x6-97449272*x3^2*x7+25133964*x3^2*x8-155000416*x3*x4^2+241474668*x3*x4*x5-15022962*x3*x4*x6-188187942*x3*x4*x7+195042506*x3*x4*x8-232066296*x3*x5^2+89037396*x3*x5*x6+116596248*x3*x5*x7+106921908*x3*x5*x8+98268042*x3*x6^2-42193750*x3*x6*x7-37290040*x3*x6*x8-49741916*x3*x7^2+139332338*x3*x7*x8-124295778*x3*x8^2-66429548*x4^3+186422156*x4^2*x5+5403312*x4^2*x6+15340828*x4^2*x7+146512338*x4^2*x8-258302790*x4*x5^2-151107524*x4*x5*x6+341726524*x4*x5*x7-143447424*x4*x5*x8+29463020*x4*x6^2+22470294*x4*x6*x7+45028932*x4*x6*x8+79504894*x4*x7^2-104377586*x4*x7*x8-82217878*x4*x8^2+245144880*x5^3+202082526*x5^2*x6-189192132*x5^2*x7-139538538*x5^2*x8-105890864*x5*x6^2-19757348*x5*x6*x7-52387956*x5*x6*x8+37062656*x5*x7^2+13700532*x5*x7*x8+70319412*x5*x8^2-41170592*x6^3+47158446*x6^2*x7+49119746*x6^2*x8-16315714*x6*x7^2+3398884*x6*x7*x8-31397374*x6*x8^2+28824892*x7^3-34981610*x7^2*x8-31955062*x7*x8^2+26519856*x8^3-9681046*x1^2-24949948*x1*x2-58476634*x1*x3+59900450*x1*x4+150572892*x1*x5-8945146*x1*x6-27146488*x1*x7-102657068*x1*x8-7437462*x2^2+80816408*x2*x3+29942696*x2*x4-196074552*x2*x5+16165674*x2*x6+20512054*x2*x7+39860986*x2*x8+30454868*x3^2+37914508*x3*x4-103227036*x3*x5-85630234*x3*x6+63766310*x3*x7-11223230*x3*x8-28638824*x4^2-78248296*x4*x5+32091662*x4*x6-54155612*x4*x7+63982956*x4*x8-106337826*x5^2+64572836*x5*x6-36184204*x5*x7+150577008*x5*x8+61209842*x6^2-5907198*x6*x7-94427370*x6*x8+13663378*x7^2-19020562*x7*x8-14053526*x8^2-7117850*x1+37469112*x2-9159396*x3-10091278*x4+140201660*x5-2277460*x6-19686100*x7-55489884*x8-29415094, 36560412*x1^3-19556350*x1^2*x2+62769566*x1^2*x3-72338396*x1^2*x4+41353090*x1^2*x5-65922968*x1^2*x6+34425500*x1^2*x7+2677416*x1^2*x8+3127784*x1*x2^2-113324492*x1*x2*x3-33492400*x1*x2*x4+31673722*x1*x2*x5+30030388*x1*x2*x6-62598140*x1*x2*x7+68945798*x1*x2*x8-56155588*x1*x3^2-159563264*x1*x3*x4+29576422*x1*x3*x5+253589224*x1*x3*x6-88861828*x1*x3*x7+124259938*x1*x3*x8+9000036*x1*x4^2-55653048*x1*x4*x5+209209160*x1*x4*x6-51961704*x1*x4*x7+40888892*x1*x4*x8+92622030*x1*x5^2-27053040*x1*x5*x6+13405428*x1*x5*x7-67090666*x1*x5*x8-163175124*x1*x6^2+110924020*x1*x6*x7-91542320*x1*x6*x8-37708764*x1*x7^2+84922720*x1*x7*x8-45935220*x1*x8^2-12659744*x2^3+81504806*x2^2*x3+41147872*x2^2*x4-18529238*x2^2*x5-23298720*x2^2*x6+6212752*x2^2*x7-55909420*x2^2*x8-1446950*x2*x3^2+130596894*x2*x3*x4-36769086*x2*x3*x5-169288340*x2*x3*x6+154043322*x2*x3*x7-70569506*x2*x3*x8+82164322*x2*x4^2-73807856*x2*x4*x5-75154456*x2*x4*x6+42828662*x2*x4*x7-110139308*x2*x4*x8-53090834*x2*x5^2-22607692*x2*x5*x6-14481992*x2*x5*x7+126277762*x2*x5*x8+175702122*x2*x6^2-208508116*x2*x6*x7-16292768*x2*x6*x8+71893362*x2*x7^2-76814952*x2*x7*x8+46455444*x2*x8^2+18546908*x3^3-459520*x3^2*x4-31044956*x3^2*x5+18859512*x3^2*x6-42365744*x3^2*x7+87590266*x3^2*x8+23831050*x3*x4^2-15022962*x3*x4*x5-155539564*x3*x4*x6+174762674*x3*x4*x7-13187428*x3*x4*x8+44518698*x3*x5^2+196536084*x3*x5*x6-42193750*x3*x5*x7-37290040*x3*x5*x8-158812314*x3*x6^2+65364520*x3*x6*x7-77634696*x3*x6*x8-1859942*x3*x7^2+59935044*x3*x7*x8-15999944*x3*x8^2+9723358*x4^3+5403312*x4^2*x5-63510256*x4^2*x6+35707034*x4^2*x7-17874420*x4^2*x8-75553762*x4*x5^2+58926040*x4*x5*x6+22470294*x4*x5*x7+45028932*x4*x5*x8+112027386*x4*x6^2-306878888*x4*x6*x7+31269640*x4*x6*x8+115369888*x4*x7^2-67836692*x4*x7*x8+30048650*x4*x8^2+67360842*x5^3-105890864*x5^2*x6-9878674*x5^2*x7-26193978*x5^2*x8-123511776*x5*x6^2+94316892*x5*x6*x7+98239492*x5*x6*x8-16315714*x5*x7^2+3398884*x5*x7*x8-31397374*x5*x8^2+90802448*x6^3-39644334*x6^2*x7-29028456*x6^2*x8-30622656*x6*x7^2-4625852*x6*x7*x8+19152552*x6*x8^2+19727252*x7^3-17882740*x7^2*x8+16996030*x7*x8^2-10756500*x8^3+63166192*x1^2-109977726*x1*x2+38133494*x1*x3-67962796*x1*x4-8945146*x1*x5-47426948*x1*x6+62193460*x1*x7-5178160*x1*x8+75291686*x2^2-55050296*x2*x3+42072966*x2*x4+16165674*x2*x5+6380140*x2*x6+20369418*x2*x7+35288154*x2*x8-39062468*x3^2-65285262*x3*x4-85630234*x3*x5+232459736*x3*x6-83491306*x3*x7+119359454*x3*x8-27321594*x4^2+32091662*x4*x5+48466052*x4*x6+39005196*x4*x7+67995312*x4*x8+32286418*x5^2+122419684*x5*x6-5907198*x5*x7-94427370*x5*x8-169466394*x6^2+83147188*x6*x7-49450996*x6*x8-12399376*x7^2+71346700*x7*x8-38996698*x8^2+113805140*x1-106242782*x2+1121510*x3-70893390*x4-2277460*x5-14212544*x6+2761390*x7+28200396*x8+44525986, -13098600*x1^3+25172512*x1^2*x2-31722484*x1^2*x3+36508884*x1^2*x4+8123308*x1^2*x5+34425500*x1^2*x6-67974848*x1^2*x7+25048172*x1^2*x8-21384966*x1*x2^2+28041300*x1*x2*x3+39313344*x1*x2*x4-5346728*x1*x2*x5-62598140*x1*x2*x6+146288536*x1*x2*x7+3573988*x1*x2*x8-45580360*x1*x3^2-39334548*x1*x3*x4+15601540*x1*x3*x5-88861828*x1*x3*x6-12879008*x1*x3*x7+37562112*x1*x3*x8-57929634*x1*x4^2-34156980*x1*x4*x5-51961704*x1*x4*x6+313021800*x1*x4*x7-31338420*x1*x4*x8-33365940*x1*x5^2+13405428*x1*x5*x6-116478672*x1*x5*x7+23248616*x1*x5*x8+55462010*x1*x6^2-75417528*x1*x6*x7+84922720*x1*x6*x8+148677984*x1*x7^2-112502776*x1*x7*x8+36328006*x1*x8^2+24595552*x2^3-30214454*x2^2*x3+1250468*x2^2*x4-10831546*x2^2*x5+6212752*x2^2*x6-2415780*x2^2*x7+25139500*x2^2*x8+54803892*x2*x3^2-77331200*x2*x3*x4-43653614*x2*x3*x5+154043322*x2*x3*x6-92259996*x2*x3*x7-27791686*x2*x3*x8-116959328*x2*x4^2+94091286*x2*x4*x5+42828662*x2*x4*x6-136904060*x2*x4*x7+115488998*x2*x4*x8+84020838*x2*x5^2-14481992*x2*x5*x6+72521572*x2*x5*x7-36267268*x2*x5*x8-104254058*x2*x6^2+143786724*x2*x6*x7-76814952*x2*x6*x8-112988184*x2*x7^2+134704252*x2*x7*x8+4439946*x2*x8^2+47754296*x3^3+187700512*x3^2*x4-97449272*x3^2*x5-42365744*x3^2*x6+152628960*x3^2*x7-152580876*x3^2*x8+85836938*x3*x4^2-188187942*x3*x4*x5+174762674*x3*x4*x6-82811836*x3*x4*x7-75421250*x3*x4*x8+58298124*x3*x5^2-42193750*x3*x5*x6-99483832*x3*x5*x7+139332338*x3*x5*x8+32682260*x3*x6^2-3719884*x3*x6*x7+59935044*x3*x6*x8+6368316*x3*x7^2-127408428*x3*x7*x8+104293580*x3*x8^2-25606524*x4^3+15340828*x4^2*x5+35707034*x4^2*x6-74437592*x4^2*x7+24785990*x4^2*x8+170863262*x4*x5^2+22470294*x4*x5*x6+159009788*x4*x5*x7-104377586*x4*x5*x8-153439444*x4*x6^2+230739776*x4*x6*x7-67836692*x4*x6*x8-232213644*x4*x7^2+279245832*x4*x7*x8-30277116*x4*x8^2-63064044*x5^3-9878674*x5^2*x6+37062656*x5^2*x7+6850266*x5^2*x8+47158446*x5*x6^2-32631428*x5*x6*x7+3398884*x5*x6*x8+86474676*x5*x7^2-69963220*x5*x7*x8-31955062*x5*x8^2-13214778*x6^3-30622656*x6^2*x7-2312926*x6^2*x8+59181756*x6*x7^2-35765480*x6*x7*x8+16996030*x6*x8^2-65676176*x7^3+100524084*x7^2*x8-31149416*x7*x8^2-2524790*x8^3+12258148*x1^2+71485992*x1*x2-31129552*x1*x3+72235344*x1*x4-27146488*x1*x5+62193460*x1*x6+7944776*x1*x7+61808112*x1*x8-63242774*x2^2-24864044*x2*x3-149608656*x2*x4+20512054*x2*x5+20369418*x2*x6-51264452*x2*x7-16662286*x2*x8+17120536*x3^2-37433952*x3*x4+63766310*x3*x5-83491306*x3*x6-9976228*x3*x7-51789322*x3*x8-27738530*x4^2-54155612*x4*x5+39005196*x4*x6-23637760*x4*x7-34077056*x4*x8-18092102*x5^2-5907198*x5*x6+27326756*x5*x7-19020562*x5*x8+41573594*x6^2-24798752*x6*x7+71346700*x6*x8-13405164*x7^2-9631480*x7*x8+23225414*x8^2-27299686*x1+49921888*x2-9248326*x3+102910436*x4-19686100*x5+2761390*x6+20606376*x7+10518710*x8-4042790, 36807028*x1^3-32979550*x1^2*x2+28819382*x1^2*x3-105952764*x1^2*x4-29449182*x1^2*x5+2677416*x1^2*x6+25048172*x1^2*x7-22125152*x1^2*x8+53575218*x1*x2^2-13455414*x1*x2*x3+49874050*x1*x2*x4-32205300*x1*x2*x5+68945798*x1*x2*x6+3573988*x1*x2*x7-15869400*x1*x2*x8+19628084*x1*x3^2+59050526*x1*x3*x4+25070814*x1*x3*x5+124259938*x1*x3*x6+37562112*x1*x3*x7+24522828*x1*x3*x8+129352852*x1*x4^2-12432286*x1*x4*x5+40888892*x1*x4*x6-31338420*x1*x4*x7-18571296*x1*x4*x8+31154022*x1*x5^2-67090666*x1*x5*x6+23248616*x1*x5*x7-74833956*x1*x5*x8-45771160*x1*x6^2+84922720*x1*x6*x7-91870440*x1*x6*x8-56251388*x1*x7^2+72656012*x1*x7*x8-52416336*x1*x8^2-6697594*x2^3-22459658*x2^2*x3-48466230*x2^2*x4+38119706*x2^2*x5-55909420*x2^2*x6+25139500*x2^2*x7+55981652*x2^2*x8-58234792*x2*x3^2-116550384*x2*x3*x4+85169574*x2*x3*x5-70569506*x2*x3*x6-27791686*x2*x3*x7+191352132*x2*x3*x8-75243320*x2*x4^2+105723362*x2*x4*x5-110139308*x2*x4*x6+115488998*x2*x4*x7+131979836*x2*x4*x8-29676360*x2*x5^2+126277762*x2*x5*x6-36267268*x2*x5*x7-176339244*x2*x5*x8-8146384*x2*x6^2-76814952*x2*x6*x7+92910888*x2*x6*x8+67352126*x2*x7^2+8879892*x2*x7*x8-64131222*x2*x8^2-23522612*x3^3-163138810*x3^2*x4+25133964*x3^2*x5+87590266*x3^2*x6-152580876*x3^2*x7+164445652*x3^2*x8-214033028*x3*x4^2+195042506*x3*x4*x5-13187428*x3*x4*x6-75421250*x3*x4*x7+273925864*x3*x4*x8+53460954*x3*x5^2-37290040*x3*x5*x6+139332338*x3*x5*x7-248591556*x3*x5*x8-38817348*x3*x6^2+59935044*x3*x6*x7-31999888*x3*x6*x8-63704214*x3*x7^2+208587160*x3*x7*x8-120260262*x3*x8^2-94914624*x4^3+146512338*x4^2*x5-17874420*x4^2*x6+24785990*x4^2*x7+145088168*x4^2*x8-71723712*x4*x5^2+45028932*x4*x5*x6-104377586*x4*x5*x7-164435756*x4*x5*x8+15634820*x4*x6^2-67836692*x4*x6*x7+60097300*x4*x6*x8+139622916*x4*x7^2-60554232*x4*x7*x8-52085880*x4*x8^2-46512846*x5^3-26193978*x5^2*x6+6850266*x5^2*x7+70319412*x5^2*x8+49119746*x5*x6^2+3398884*x5*x6*x7-62794748*x5*x6*x8-34981610*x5*x7^2-63910124*x5*x7*x8+79559568*x5*x8^2-9676152*x6^3-2312926*x6^2*x7+19152552*x6^2*x8-17882740*x6*x7^2+33992060*x6*x7*x8-32269500*x6*x8^2+33508028*x7^3-31149416*x7^2*x8-7574370*x7*x8^2+6878656*x8^3+4124432*x1^2+28406168*x1*x2+75052760*x1*x3+70635188*x1*x4-102657068*x1*x5-5178160*x1*x6+61808112*x1*x7-81952748*x1*x8-30387896*x2^2-100953048*x2*x3-64014352*x2*x4+39860986*x2*x5+35288154*x2*x6-16662286*x2*x7+83985924*x2*x8-48907266*x3^2-102869128*x3*x4-11223230*x3*x5+119359454*x3*x6-51789322*x3*x7+100801104*x3*x8-73965966*x4^2+63982956*x4*x5+67995312*x4*x6-34077056*x4*x7+106968244*x4*x8+75288504*x5^2-94427370*x5*x6-19020562*x5*x7-28107052*x5*x8-24725498*x6^2+71346700*x6*x7-77993396*x6*x8-4815740*x7^2+46450828*x7*x8-36536238*x8^2+51416068*x1+3555814*x2+30861670*x3-15378600*x4-55489884*x5+28200396*x6+10518710*x7-20449672*x8+13316022];
id = ideal(P,F);
gb = gen_fglm(id, target_order=:degrevlex);
display(gb)
exit()
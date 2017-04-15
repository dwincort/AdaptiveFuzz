
import Control.Monad
import Text.Read (readMaybe)



--age is 12
--ancstry1 is lst!!35
--avail is 47
--citizen is 53
--class is 54
--disabl1 is 56
--english is 58
--fertil is 60
--hours per week is 62
--immigr is 64
--income1 is 65
--industry is 73
--marital is 78
--means is 80 (means of transportation to work)
--military is 83
--occup is 86
--pob is 89
--race is 94
--total pers. earnings is 96
--total person income is 104
--rpob is 105
--rspouse is 107
--rvetserv is 108
--sex is 112
--weeks worked is 118
--education is 122

showNum :: Double -> String
showNum n | n <= 0 = "0.0"
showNum n | n >= 1 = "1.0"
showNum n = show n --"0." ++ show (round (100 * n))


-- 23 groups
discOccup :: Int -> [Double]
discOccup n | n==0  = replicate 23 0   -- n/a
discOccup n | n<43  = discretize 22 0  -- 000-042   Executive, Administrative, and Managerial Occupations
discOccup n | n<203 = discretize 22 1  -- 043-202   Professional Specialty Occupations
discOccup n | n<243 = discretize 22 2  -- 203-242   Technicians and Related Support Occupations
discOccup n | n<303 = discretize 22 3  -- 243-302   Sales Occupations
discOccup n | n<403 = discretize 22 4  -- 303-402   Administrative Support Occupations, Including Clerical
discOccup n | n<413 = discretize 22 5  -- 403-412   Private Household Occupations
discOccup n | n<433 = discretize 22 6  -- 413-432   Protective Service Occupations
discOccup n | n<473 = discretize 22 7  -- 433-472   Service Occupations, Except Protective and Household
discOccup n | n<477 = discretize 22 8  -- 473-476     Farm Operators and Managers
discOccup n | n<494 = discretize 22 9  -- 477-493     Other Agricultural and Related Occupations
discOccup n | n<497 = discretize 22 10 -- 494-496   Forestry and Logging Occupations
discOccup n | n<503 = discretize 22 11 -- 497-502   Fishers, Hunters, and Trappers
discOccup n | n<553 = discretize 22 12 -- 503-552   Mechanics and Repairers
discOccup n | n<613 = discretize 22 13 -- 553-612     Construction Trades
discOccup n | n<628 = discretize 22 14 -- 613-627     Extractive Occupations
discOccup n | n<703 = discretize 22 15 -- 628-702     Precision Production Occupations
discOccup n | n<803 = discretize 22 16 -- 703-802   Machine Operators, Assemblers, and Inspectors
discOccup n | n<874 = discretize 22 17 -- 803-863     Transportation and Material Moving Occupations
discOccup n | n<903 = discretize 22 18 -- 864-902   Handlers, Equipment Cleaners, Helpers, and Laborers
discOccup n | n<904 = discretize 22 19 -- 903       Commissioned officers and warrant officers
discOccup n | n<905 = discretize 22 20 -- 904       Non-commissioned officers and other enlisted personnel
discOccup n | n<909 = discretize 22 21 -- 905-908   Military occupation, rank not specified
discOccup n         = discretize 22 22 -- 909-999   Unemployed, last worked 1984 or earlier

-- 36 groups
discRace :: Int -> [Double]
discRace n | n<3  = discretize 35 (n-1) --white and black are 0 and 1
discRace n | n<37 = discretize 35 (n-2) --all races except native american (race 3 is weirdly missing)
discRace n | n==37 = replicate 36 0     --don't bother with "other race", set all to 0
discRace n = discretize 35 35           --native americans all grouped together as the last entry
-- 001     White 800 869, 971
-- 002     Black 870 934, 972
-- 004     Eskimo 935 940, 974
-- 005     Aleut 941 970, 975
-- 006     Chinese, Except Taiwanese 605, 976
-- 007     Taiwanese 606, 607
-- 008     Filipino 608, 977
-- 009     Japanese 611, 981
-- 010     Asian Indian 600, 982
-- 011     Korean 612, 979
-- 012     Vietnamese 619, 980
-- 013     Cambodian 604
-- 014     Hmong 609
-- 015     Laotian 613
-- 016     Thai 618
-- 017     Bangladeshi 601
-- 018     Burmese 603
-- 019     Indonesian 610
-- 020     Malayan 614
-- 021     Okinawan 615
-- 022     Pakistani 616
-- 023     Sri Lankan 617
-- 024     All Other Asian 602, 620 652, 985
-- 025     Hawaiian 653, 654, 978
-- 026     Samoan 655, 983
-- 027     Tahitian 656
-- 028     Tongan 657
-- 029     Other Polynesian 658, 659
-- 030     Guamanian 660, 984
-- 031     Northern Mariana Islander 661, 671, 673
-- 032     Palauan 663
-- 033     Other Micronesian 662, 664 670, 672, 674
-- 034     Fijian 676
-- 035     Other Melanesian 677 680
-- 036     Pacific Islander, Not Specified 681 699
-- 037     Other Race 700 799, 986 999

-- 15 groups
discIndustry :: Int -> [Double]
discIndustry n | n==0  = replicate 15 0   -- n/a
discIndustry n | n<40  = discretize 14 0  -- 000-039       AGRICULTURE, FORESTRY, AND FISHERIES
discIndustry n | n<60  = discretize 14 1  -- 040-059       MINING
discIndustry n | n<100 = discretize 14 2  -- 060-099       CONSTRUCTION (15, 16, 17)
discIndustry n | n<400 = discretize 14 3  -- 100-399       MANUFACTURING
discIndustry n | n<500 = discretize 14 4  -- 400-499       TRANSPORTATION, COMMUNICATIONS, AND OTHER PUBLIC UTILITIES
discIndustry n | n<580 = discretize 14 5  -- 500-579       WHOLESALE TRADE
discIndustry n | n<700 = discretize 14 6  -- 580-699       RETAIL TRADE
discIndustry n | n<721 = discretize 14 7  -- 700-720       FINANCE, INSURANCE, AND REAL ESTATE
discIndustry n | n<770 = discretize 14 8  -- 721-760       BUSINESS AND REPAIR SERVICES
discIndustry n | n<800 = discretize 14 9  -- 761-799       PERSONAL SERVICES
discIndustry n | n<812 = discretize 14 10 -- 800-811       ENTERTAINMENT AND RECREATION SERVICES
discIndustry n | n<900 = discretize 14 11 -- 812-899       PROFESSIONAL AND RELATED SERVICES
discIndustry n | n<940 = discretize 14 12 -- 900-939       PUBLIC ADMINISTRATION
discIndustry n | n<992 = discretize 14 13 -- 940-991       ACTIVE DUTY MILITARY
discIndustry n         = discretize 14 14 -- 992-999       EXPERIENCED UNEMPLOYED NOT CLASSIFIED BY INDUSTRY

-- 14 groups
discRPob n = maybe (replicate 14 0) (discretize 13) x where
    x = case n of
         10 -> Just 0  -- Born in State of Res.
         21 -> Just 1  -- Northeast
         22 -> Just 2  -- Midwest
         23 -> Just 3  -- South
         24 -> Just 4  -- West
         31 -> Just 5  -- Puerto Rico
         32 -> Just 6  -- American Samoa
         33 -> Just 7  -- Guam
         34 -> Just 8  -- Northern Marianas
         35 -> Just 9  -- Us Virgin Islands
         36 -> Just 10 -- Elsewhere
         40 -> Just 11 -- Born Abroad of American Parents
         51 -> Just 12 -- Naturalized Citizen
         52 -> Just 13 -- Not a Citizen
         _ -> Nothing -- unknown response

-- 1 continuous plus 7 groups
discEducation n | n<11 = (fromIntegral n)/10 : replicate 7 0
discEducation n = 1 : discretize 6 (n-11)
-- 00 through 09 indicates none through some level of grade school, turned into a continuous value
-- 10      High School Graduate, Diploma or Ged
-- 11      Some Coll., But No Degree
-- 12      Associate Degree in Coll., Occupational
-- 13      Associate Degree in Coll., Academic Prog
-- 14      Bachelors Degree
-- 15      Masters Degree
-- 16      Professional Degree
-- 17      Doctorate Degree



-- given a number max and an index e, produces a list that is (max+1) length
-- that is 0 in every entry except thee e-th one.
discretize :: Int -> Int -> [Double]
discretize max e = replicate e 0 ++ (1 : replicate (max-e) 0)


restructure :: String -> String
restructure s = 
    let lst = map (read :: String -> Int) (words s)
        newlst =
           (fromIntegral (lst!!104) / 401000):  --total person income
           -------------------------------------------------------------
           (fromIntegral (lst!!112)):           --sex (0=male, 1=female)
           (if (lst!!56) == 1 then 1 else 0):   --disabl1
           (fromIntegral (lst!!12) / 90):       --age
           (fromIntegral (lst!!58) / 4):        --english (0 is fluent, 1 is non-speaking)
           (fromIntegral (lst!!62) / 99):       --hours per week
           (fromIntegral (lst!!118) / 52):      --weeks worked
           (fromIntegral (lst!!65) / 140000):   --income1
           (fromIntegral (lst!!66) / 90000):    --income2
           (fromIntegral (lst!!67) / 54000):    --income3
           (fromIntegral (lst!!68) / 40000):    --income4
           (fromIntegral (lst!!69) / 17000):    --income5
           (fromIntegral (lst!!70) / 10000):    --income6
           (fromIntegral (lst!!71) / 30000):    --income7
           (fromIntegral (lst!!72) / 20000):    --income8
           (discEducation (lst!!122)) ++        --education years
           (discretize 9 (lst!!54)) ++          --work class
           (discretize 12 (lst!!80)) ++         --means of transportation to work
           (discretize 4 (lst!!83)) ++          --military service
           (discretize 6 (lst!!107)) ++         --marital status (rspouse)
           (discOccup (lst!!86)) ++             --occupation
           (discRace (lst!!94)) ++              --race
           (discRPob (lst!!105)) ++             --place of birth
           (discIndustry (lst!!73))             --industry position
    in unwords (map showNum newlst)


main = do
    d <- readFile "USCensus1990raw.data"
    let strs = map restructure (lines d)
    mapM_ (\s -> appendFile "USCensus1990CC.data" ('\n':s)) strs


-- excluding total person income,
-- 2 + 12 + 8 + 10 + 13 + 5 + 7 + 23 + 36 + 14 + 15 = 145 columns
-- the first 2 are straight-up booleans, 
-- the next 13 are mostly continuous, 
-- the next 130 are essentially boolean valued continuous-zations of discrete entries

checkFile = do
    d <- readFile "testdata.data"
    let strs = zip [1..] (lines d)
    forM_ strs (\(i,s) -> if good s then return () else putStrLn ("Line "++show i++": "++s))
    where good s = dubs s && lenRight s
          dubs s = all id $ map ((maybe False (const True)) . (readMaybe :: String -> Maybe Double)) (words s)
          lenRight s = length (words s) == 146


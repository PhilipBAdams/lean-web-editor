module ExportedParser exposing (..)

import Parser exposing (..)
import Set

type Info = BD
          | BI
          | BS
          | BC
            
type alias Intro = {name : Int, typeof : Int} 
                    
type alias DEFEntry = {id : Int, typeof : Int, value : Int, params : List Int}                  
type alias AXEntry = {id : Int, typeof : Int, params : List Int}
type alias INDHelpEntry = {num : Int, id: Int, typeof : Int, num_intros : Int, introsAndParams : List Int}
type alias INDEntry = {id: Int, typeof : Int, intros : List Intro, params : List Int}

type alias NSEntry = {id : Int, prev : Int, name : String}
type alias NIEntry = {id : Int, prev : Int, name : Int}

type alias USEntry = {id : Int, prev : Int}
type alias UMEntry = {id : Int, prev1 : Int, prev2 : Int}
type alias UPEntry = {id : Int, name : Int}

type alias EVEntry = {id : Int, bound : Int}
type alias ESEntry = {id : Int, univ : Int}
type alias ECEntry = {id : Int, name : Int, params : List Int}
type alias EAEntry = {id : Int, function : Int, arg : Int}
type alias EPEntry = {id : Int, info : Info, binder_name : Int, typeof : Int, body : Int}
    
type Term = -- NAMES
            NS NSEntry
          | NI NIEntry
          -- UNIVERSES
          | US USEntry
          | UM UMEntry
          | UIM UMEntry
          | UP UPEntry
          -- EXPRESSIONS
          | EV EVEntry
          | ES ESEntry
          | EC ECEntry
          | EA EAEntry
          | EL EPEntry
          | EP EPEntry
          -- DEFINITIONS
          | DEF DEFEntry
          -- AXIOMS
          | AX AXEntry
          -- INDUCTION
          | IND INDEntry
          -- QUOTIENT TYPES
          | QUOT
          -- Parse Errors
          | ParseError


parseInfo : Parser Info
parseInfo =
    oneOf
        [succeed BD
        |. symbol "#BD"
        , succeed BI
        |. symbol "#BI"
        , succeed BS
        |. symbol "#BS"
        , succeed BC
        |. symbol "#BC"]
        
-- Note that negative inputs will parse until end of input
parseKInts : Int -> Parser (List Int)
parseKInts k =
    loop (k,[]) intsHelp
    
parseInts : Parser (List Int)
parseInts =
    loop (-1,[]) intsHelp

intsHelp : (Int, List Int) -> Parser (Step (Int, List Int) (List Int))
intsHelp (k, revInts) =
    case k of
        0 -> succeed () |>  map (\_ -> Done (List.reverse revInts))
        _ -> oneOf
             [ succeed (\num -> Loop (k-1, num :: revInts))
             |= int
             |. spaces
             , succeed ()
             |> map (\_ -> Done (List.reverse revInts))]
           
parseDEF : Parser DEFEntry
parseDEF =
    succeed DEFEntry
        |. spaces
        |= int
        |. spaces
        |= int
        |. spaces
        |= int
        |. spaces
        |= parseInts

parseAX : Parser AXEntry
parseAX =
    succeed AXEntry
        |. spaces
        |= int
        |. spaces
        |= int
        |. spaces
        |= parseInts

toIntros : List Int -> List Intro
toIntros xs =
    case xs of
        (x::(y :: rest)) -> {name = x, typeof = y} :: toIntros rest
        _ -> []
    
indHelptoIND : INDHelpEntry -> Parser INDEntry
indHelptoIND {num, id, typeof, num_intros, introsAndParams} =
    succeed {id=id
    , typeof=typeof
    , intros = toIntros (List.take (2*num_intros) introsAndParams)
    , params = (List.drop (2*num_intros) introsAndParams)}

parseIND : Parser INDEntry
parseIND =
    succeed INDHelpEntry
        |. spaces
        |= int
        |. spaces
        |= int
        |. spaces
        |= int
        |. spaces
        |= int
        |. spaces
        |= parseInts
        |> andThen indHelptoIND
        
parseNS : Parser NSEntry
parseNS =
    backtrackable <|
        succeed NSEntry
            |= int
            |. spaces
            |. symbol "#NS"
            |. spaces
            |= int
            |. spaces
            |= (Parser.getChompedString <| Parser.chompUntilEndOr "\n")

parseNI : Parser NIEntry
parseNI =
    backtrackable <|
        succeed NIEntry
            |= int
            |. spaces
            |. symbol "#NI"
            |. spaces
            |= int
            |. spaces
            |= int


parseUS : Parser USEntry
parseUS =
    backtrackable <|
        succeed USEntry
            |= int
            |. spaces
            |. symbol "#US"
            |. spaces
            |= int

parseUM : Parser UMEntry
parseUM =
    backtrackable <|
        succeed UMEntry
            |= int
            |. spaces
            |. symbol "#UM"
            |. spaces
            |= int
            |. spaces
            |= int

parseUIM : Parser UMEntry
parseUIM =
    backtrackable <|
        succeed UMEntry
            |= int
            |. spaces
            |. symbol "#UIM"
            |. spaces
            |= int
            |. spaces
            |= int

parseUP : Parser UPEntry       
parseUP =
    backtrackable <|
        succeed UPEntry
            |= int
            |. spaces
            |. symbol "#UP"
            |. spaces
            |= int

parseEV : Parser EVEntry
parseEV =
    backtrackable <|
        succeed EVEntry
            |= int
            |. spaces
            |. symbol "#EV"
            |. spaces
            |= int

parseES : Parser ESEntry
parseES =
    backtrackable <|
        succeed ESEntry
            |= int
            |. spaces
            |. symbol "#ES"
            |. spaces
            |= int
            

parseEC : Parser ECEntry               
parseEC =
    backtrackable <|
        succeed ECEntry
            |= int
            |. spaces
            |. symbol "#EC"
            |. spaces
            |= int
            |. spaces
            |= parseInts
               
parseEA : Parser EAEntry               
parseEA =
    backtrackable <|
        succeed EAEntry
            |= int
            |. spaces
            |. symbol "#EA"
            |. spaces
            |= int
            |. spaces
            |= int
            
parseEL : Parser EPEntry
parseEL =
    backtrackable <|
        succeed EPEntry
            |= int
            |. spaces
            |. symbol "#EL"
            |. spaces
            |= parseInfo
            |. spaces
            |= int
            |. spaces
            |= int
            |. spaces
            |= int
               
parseEP : Parser EPEntry
parseEP =
    backtrackable <|
        succeed EPEntry
            |= int
            |. spaces
            |. symbol "#EP"
            |. spaces
            |= parseInfo
            |. spaces
            |= int
            |. spaces
            |= int
            |. spaces
            |= int

parseTerm : Parser Term
parseTerm =
    oneOf
    [succeed DEF
    |. keyword "#DEF"
    |= parseDEF
    , succeed AX
    |. keyword "#AX"
    |= parseAX
    , succeed IND
    |. keyword "#IND"
    |= parseIND
    , succeed QUOT
    |. keyword "#QUOT"
    , succeed NS
    |= parseNS
    , succeed NI
    |= parseNI
    , succeed US
    |= parseUS
    ,succeed UM
    |= parseUM
    , succeed UIM
    |= parseUIM
    , succeed UP
    |= parseUP
    , succeed EV
    |= parseEV
    , succeed ES
    |= parseES
    , succeed EC
    |= parseEC
    , succeed EA
    |= parseEA
    , succeed EL
    |= parseEL
    , succeed EP
    |= parseEP
    , succeed ParseError
    |. Parser.chompUntilEndOr "\n"]


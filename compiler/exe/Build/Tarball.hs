{-# LANGUAGE OverloadedStrings #-}

module Build.Tarball (
    createProjectTarball,
    extractProjectTarball,
    TarballOptions (..),
    TarballContents (..),
    tarballExtension,
    defaultTarballOptions,
) where

import Alloy.Ir (AlloyModule (amName))
import Build.Metadata (ProjectMetadata, SerializableConstructorMetadata, SerializableName, createProjectMetadata)
import qualified Codec.Archive.Tar as Tar
import qualified Codec.Archive.Tar.Entry as TarEntry
import qualified Codec.Compression.GZip as GZip
import Data.Aeson (decode, encode)
import qualified Data.Binary
import qualified Data.ByteString.Lazy as BL
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Orphans.Binary ()
import Project.Symbols (Symbol)
import System.FilePath (takeFileName, (</>))
import Typing.Types (QualifiedType)

tarballExtension :: String
tarballExtension = ".toria"

data TarballOptions = TarballOptions
    { includeObjects :: Bool
    , includeLLVM :: Bool
    , compress :: Bool
    }
    deriving (Show, Eq)

defaultTarballOptions :: TarballOptions
defaultTarballOptions =
    TarballOptions
        { includeObjects = True
        , includeLLVM = True
        , compress = True
        }

data TarballContents = TarballContents
    { tcMetadata :: ProjectMetadata
    , tcObjectFiles :: [(FilePath, BL.ByteString)]
    , tcLLVMFiles :: [(FilePath, BL.ByteString)]
    , tcAlloyModules :: [AlloyModule]
    }
    deriving (Show)

createProjectTarball ::
    FilePath ->
    TarballOptions ->
    String ->
    String ->
    [FilePath] ->
    Map.Map Symbol QualifiedType ->
    [(QualifiedType, Bool)] ->
    Map.Map String [String] ->
    Map.Map SerializableName SerializableConstructorMetadata ->
    [(FilePath, BL.ByteString)] ->
    [(FilePath, BL.ByteString)] ->
    [AlloyModule] ->
    IO ()
createProjectTarball outPath opts modName version srcFiles publicSyms publicInsts depGraph constructors objFiles llvmFiles alloyModules = do
    let metadata = createProjectMetadata modName version srcFiles publicSyms publicInsts depGraph constructors
    let metadataJson = encode metadata

    let objFilesBS = [(path, content) | (path, content) <- objFiles]
    let llvmFilesBS = [(path, content) | (path, content) <- llvmFiles]

    let entries =
            concat
                [ [createMetadataEntry metadataJson]
                , if includeObjects opts then map createObjectEntry objFilesBS else []
                , if includeLLVM opts then map createLLVMEntry llvmFilesBS else []
                , map createAlloyEntry alloyModules
                ]

    let tarball = Tar.write entries
    let output = if compress opts then GZip.compress tarball else tarball

    BL.writeFile outPath output
    putStrLn $ "Created tarball: " ++ outPath

extractProjectTarball :: FilePath -> IO (Either String TarballContents)
extractProjectTarball tarPath = do
    compressed <- BL.readFile tarPath
    let decompressed =
            if isGzipped compressed
                then GZip.decompress compressed
                else compressed

    case Tar.read decompressed of
        Tar.Fail err -> return $ Left $ "Failed to read tarball: " ++ show err
        Tar.Done -> return $ Left "Empty tarball"
        entries -> extractContents entries

isGzipped :: BL.ByteString -> Bool
isGzipped bs = BL.take 2 bs == BL.pack [0x1f, 0x8b]

extractContents :: Tar.Entries Tar.FormatError -> IO (Either String TarballContents)
extractContents entries = do
    let entryList = Tar.foldEntries (:) [] (\err -> error $ "Tar error: " ++ show err) entries
    case findMetadata entryList of
        Nothing -> return $ Left "metadata.json not found in tarball"
        Just metadataBS -> case decode metadataBS of
            Nothing -> return $ Left "Failed to parse metadata.json"
            Just metadata -> do
                let objFiles = extractFromDir "objects" entryList
                let llvmFiles = extractFromDir "llvm" entryList
                alloyModules <- extractAlloyModules entryList
                return
                    $ Right
                        TarballContents
                            { tcMetadata = metadata
                            , tcObjectFiles = objFiles
                            , tcLLVMFiles = llvmFiles
                            , tcAlloyModules = alloyModules
                            }

findMetadata :: [Tar.Entry] -> Maybe BL.ByteString
findMetadata entries =
    case mapMaybe (\entry -> if Tar.entryPath entry == "metadata.json" then getContent entry else Nothing) entries of
        (c : _) -> Just c
        [] -> Nothing

extractFromDir :: FilePath -> [Tar.Entry] -> [(FilePath, BL.ByteString)]
extractFromDir dir = mapMaybe extractFile
  where
    extractFile entry =
        let path = Tar.entryPath entry
            prefix = dir ++ "/"
        in if take (length prefix) path == prefix
            then do
                content <- getContent entry
                return (drop (length prefix) path, content)
            else Nothing

extractAlloyModules :: [Tar.Entry] -> IO [AlloyModule]
extractAlloyModules entries = do
    let alloyEntries =
            filter
                ( \entry ->
                    take 6 (Tar.entryPath entry)
                        == "alloy/"
                )
                entries
    let alloyModules = mapMaybe extractAlloyModule alloyEntries
    return alloyModules

extractAlloyModule :: Tar.Entry -> Maybe AlloyModule
extractAlloyModule entry = do
    content <- getContent entry
    case Data.Binary.decodeOrFail content of
        Left _ -> Nothing
        Right (_, _, alloyModule) -> Just alloyModule

getContent :: Tar.Entry -> Maybe BL.ByteString
getContent entry = case Tar.entryContent entry of
    Tar.NormalFile bs _ -> Just bs
    _ -> Nothing

createMetadataEntry :: BL.ByteString -> Tar.Entry
createMetadataEntry content =
    case TarEntry.toTarPath False "metadata.json" of
        Left err -> error $ "Invalid tar path for metadata.json: " ++ err
        Right tarPath ->
            TarEntry.simpleEntry tarPath (Tar.NormalFile content (fromIntegral $ BL.length content))

createObjectEntry :: (FilePath, BL.ByteString) -> Tar.Entry
createObjectEntry (path, content) =
    let filename = takeFileName path
        entryPath = "objects" </> filename
    in case TarEntry.toTarPath False entryPath of
        Left err -> error $ "Invalid tar path for object: " ++ entryPath ++ ": " ++ err
        Right tarPath ->
            TarEntry.simpleEntry tarPath (Tar.NormalFile content (fromIntegral $ BL.length content))

createLLVMEntry :: (FilePath, BL.ByteString) -> Tar.Entry
createLLVMEntry (path, content) =
    let filename = takeFileName path
        entryPath = "llvm" </> filename
    in case TarEntry.toTarPath False entryPath of
        Left err -> error $ "Invalid tar path for LLVM: " ++ entryPath ++ ": " ++ err
        Right tarPath ->
            TarEntry.simpleEntry tarPath (Tar.NormalFile content (fromIntegral $ BL.length content))

createAlloyEntry :: AlloyModule -> Tar.Entry
createAlloyEntry alloyMod =
    let entryPath = "alloy" </> amName alloyMod ++ ".alloybin"
        content = Data.Binary.encode alloyMod
    in case TarEntry.toTarPath False entryPath of
        Left err -> error $ "Invalid tar path for alloy: " ++ entryPath ++ ": " ++ err
        Right tarPath ->
            TarEntry.simpleEntry tarPath (Tar.NormalFile content (fromIntegral $ BL.length content))

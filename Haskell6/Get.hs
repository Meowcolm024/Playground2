{-# LANGUAGE OverloadedStrings #-}
import           Control.Monad.IO.Class
import qualified Data.ByteString.Char8
import           Data.Text
import           Network.HTTP.Req

tok = Data.ByteString.Char8.pack "accesstoken"
main :: IO ()
main =
    runReq defaultHttpConfig { httpConfigCheckResponse = \_ _ _ -> Nothing }
        $ do
              v <- req
                  GET
                  (  https "127.0.0.1:9000"
                  /: "/v2beta1"
                  /: "json-schema"
                  /: "entity"
                  /: "local"
                  /: "Person"
                  /: "zhangsan"
                  )
                  NoReqBody
                  bsResponse
                  (  "fields"
                  =: ("streamerConnectionInfo" :: Text)
                  <> oAuth2Bearer tok
                  )
              liftIO $ Data.ByteString.Char8.putStrLn (responseBody v)

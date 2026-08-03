{- This file was auto-generated from Perf.proto by the proto-lens-protoc program. -}
{-# LANGUAGE ScopedTypeVariables, DataKinds, TypeFamilies, UndecidableInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, PatternSynonyms, MagicHash, NoImplicitPrelude, DataKinds, BangPatterns, TypeApplications, OverloadedStrings, DerivingStrategies#-}
{-# OPTIONS_GHC -Wno-unused-imports#-}
{-# OPTIONS_GHC -Wno-duplicate-exports#-}
{-# OPTIONS_GHC -Wno-dodgy-exports#-}
module Proto.Perf (
        Batch(), Item(), Meta()
    ) where
import qualified Data.ProtoLens.Runtime.Control.DeepSeq as Control.DeepSeq
import qualified Data.ProtoLens.Runtime.Data.ProtoLens.Prism as Data.ProtoLens.Prism
import qualified Data.ProtoLens.Runtime.Prelude as Prelude
import qualified Data.ProtoLens.Runtime.Data.Int as Data.Int
import qualified Data.ProtoLens.Runtime.Data.Monoid as Data.Monoid
import qualified Data.ProtoLens.Runtime.Data.Word as Data.Word
import qualified Data.ProtoLens.Runtime.Data.ProtoLens as Data.ProtoLens
import qualified Data.ProtoLens.Runtime.Data.ProtoLens.Encoding.Bytes as Data.ProtoLens.Encoding.Bytes
import qualified Data.ProtoLens.Runtime.Data.ProtoLens.Encoding.Growing as Data.ProtoLens.Encoding.Growing
import qualified Data.ProtoLens.Runtime.Data.ProtoLens.Encoding.Parser.Unsafe as Data.ProtoLens.Encoding.Parser.Unsafe
import qualified Data.ProtoLens.Runtime.Data.ProtoLens.Encoding.Wire as Data.ProtoLens.Encoding.Wire
import qualified Data.ProtoLens.Runtime.Data.ProtoLens.Field as Data.ProtoLens.Field
import qualified Data.ProtoLens.Runtime.Data.ProtoLens.Message.Enum as Data.ProtoLens.Message.Enum
import qualified Data.ProtoLens.Runtime.Data.ProtoLens.Service.Types as Data.ProtoLens.Service.Types
import qualified Data.ProtoLens.Runtime.Lens.Family2 as Lens.Family2
import qualified Data.ProtoLens.Runtime.Lens.Family2.Unchecked as Lens.Family2.Unchecked
import qualified Data.ProtoLens.Runtime.Data.Text as Data.Text
import qualified Data.ProtoLens.Runtime.Data.Map as Data.Map
import qualified Data.ProtoLens.Runtime.Data.ByteString as Data.ByteString
import qualified Data.ProtoLens.Runtime.Data.ByteString.Char8 as Data.ByteString.Char8
import qualified Data.ProtoLens.Runtime.Data.Text.Encoding as Data.Text.Encoding
import qualified Data.ProtoLens.Runtime.Data.Vector as Data.Vector
import qualified Data.ProtoLens.Runtime.Data.Vector.Generic as Data.Vector.Generic
import qualified Data.ProtoLens.Runtime.Data.Vector.Unboxed as Data.Vector.Unboxed
import qualified Data.ProtoLens.Runtime.Text.Read as Text.Read
{- | Fields :

         * 'Proto.Perf_Fields.items' @:: Lens' Batch [Item]@
         * 'Proto.Perf_Fields.vec'items' @:: Lens' Batch (Data.Vector.Vector Item)@
         * 'Proto.Perf_Fields.label' @:: Lens' Batch Data.Text.Text@ -}
data Batch
  = Batch'_constructor {_Batch'items :: !(Data.Vector.Vector Item),
                        _Batch'label :: !Data.Text.Text,
                        _Batch'_unknownFields :: !Data.ProtoLens.FieldSet}
  deriving stock (Prelude.Eq, Prelude.Ord)
instance Prelude.Show Batch where
  showsPrec _ __x __s
    = Prelude.showChar
        '{'
        (Prelude.showString
           (Data.ProtoLens.showMessageShort __x) (Prelude.showChar '}' __s))
instance Data.ProtoLens.Field.HasField Batch "items" [Item] where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Batch'items (\ x__ y__ -> x__ {_Batch'items = y__}))
        (Lens.Family2.Unchecked.lens
           Data.Vector.Generic.toList
           (\ _ y__ -> Data.Vector.Generic.fromList y__))
instance Data.ProtoLens.Field.HasField Batch "vec'items" (Data.Vector.Vector Item) where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Batch'items (\ x__ y__ -> x__ {_Batch'items = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Batch "label" Data.Text.Text where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Batch'label (\ x__ y__ -> x__ {_Batch'label = y__}))
        Prelude.id
instance Data.ProtoLens.Message Batch where
  messageName _ = Data.Text.pack "bench.perf.Batch"
  packedMessageDescriptor _
    = "\n\
      \\ENQBatch\DC2&\n\
      \\ENQitems\CAN\SOH \ETX(\v2\DLE.bench.perf.ItemR\ENQitems\DC2\DC4\n\
      \\ENQlabel\CAN\STX \SOH(\tR\ENQlabel"
  packedFileDescriptor _ = packedFileDescriptor
  fieldsByTag
    = let
        items__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "items"
              (Data.ProtoLens.MessageField Data.ProtoLens.MessageType ::
                 Data.ProtoLens.FieldTypeDescriptor Item)
              (Data.ProtoLens.RepeatedField
                 Data.ProtoLens.Unpacked (Data.ProtoLens.Field.field @"items")) ::
              Data.ProtoLens.FieldDescriptor Batch
        label__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "label"
              (Data.ProtoLens.ScalarField Data.ProtoLens.StringField ::
                 Data.ProtoLens.FieldTypeDescriptor Data.Text.Text)
              (Data.ProtoLens.PlainField
                 Data.ProtoLens.Optional (Data.ProtoLens.Field.field @"label")) ::
              Data.ProtoLens.FieldDescriptor Batch
      in
        Data.Map.fromList
          [(Data.ProtoLens.Tag 1, items__field_descriptor),
           (Data.ProtoLens.Tag 2, label__field_descriptor)]
  unknownFields
    = Lens.Family2.Unchecked.lens
        _Batch'_unknownFields
        (\ x__ y__ -> x__ {_Batch'_unknownFields = y__})
  defMessage
    = Batch'_constructor
        {_Batch'items = Data.Vector.Generic.empty,
         _Batch'label = Data.ProtoLens.fieldDefault,
         _Batch'_unknownFields = []}
  parseMessage
    = let
        loop ::
          Batch
          -> Data.ProtoLens.Encoding.Growing.Growing Data.Vector.Vector Data.ProtoLens.Encoding.Growing.RealWorld Item
             -> Data.ProtoLens.Encoding.Bytes.Parser Batch
        loop x mutable'items
          = do end <- Data.ProtoLens.Encoding.Bytes.atEnd
               if end then
                   do frozen'items <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                        (Data.ProtoLens.Encoding.Growing.unsafeFreeze mutable'items)
                      (let missing = []
                       in
                         if Prelude.null missing then
                             Prelude.return ()
                         else
                             Prelude.fail
                               ((Prelude.++)
                                  "Missing required fields: "
                                  (Prelude.show (missing :: [Prelude.String]))))
                      Prelude.return
                        (Lens.Family2.over
                           Data.ProtoLens.unknownFields
                           (\ !t -> Prelude.reverse t)
                           (Lens.Family2.set
                              (Data.ProtoLens.Field.field @"vec'items") frozen'items x))
               else
                   do tag <- Data.ProtoLens.Encoding.Bytes.getVarInt
                      case tag of
                        10
                          -> do !y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                        (do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                            Data.ProtoLens.Encoding.Bytes.isolate
                                              (Prelude.fromIntegral len)
                                              Data.ProtoLens.parseMessage)
                                        "items"
                                v <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                       (Data.ProtoLens.Encoding.Growing.append mutable'items y)
                                loop x v
                        18
                          -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       (do value <- do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                                       Data.ProtoLens.Encoding.Bytes.getBytes
                                                         (Prelude.fromIntegral len)
                                           Data.ProtoLens.Encoding.Bytes.runEither
                                             (case Data.Text.Encoding.decodeUtf8' value of
                                                (Prelude.Left err)
                                                  -> Prelude.Left (Prelude.show err)
                                                (Prelude.Right r) -> Prelude.Right r))
                                       "label"
                                loop
                                  (Lens.Family2.set (Data.ProtoLens.Field.field @"label") y x)
                                  mutable'items
                        wire
                          -> do !y <- Data.ProtoLens.Encoding.Wire.parseTaggedValueFromWire
                                        wire
                                loop
                                  (Lens.Family2.over
                                     Data.ProtoLens.unknownFields (\ !t -> (:) y t) x)
                                  mutable'items
      in
        (Data.ProtoLens.Encoding.Bytes.<?>)
          (do mutable'items <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                 Data.ProtoLens.Encoding.Growing.new
              loop Data.ProtoLens.defMessage mutable'items)
          "Batch"
  buildMessage
    = \ _x
        -> (Data.Monoid.<>)
             (Data.ProtoLens.Encoding.Bytes.foldMapBuilder
                (\ _v
                   -> (Data.Monoid.<>)
                        (Data.ProtoLens.Encoding.Bytes.putVarInt 10)
                        ((Prelude..)
                           (\ bs
                              -> (Data.Monoid.<>)
                                   (Data.ProtoLens.Encoding.Bytes.putVarInt
                                      (Prelude.fromIntegral (Data.ByteString.length bs)))
                                   (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                           Data.ProtoLens.encodeMessage
                           _v))
                (Lens.Family2.view (Data.ProtoLens.Field.field @"vec'items") _x))
             ((Data.Monoid.<>)
                (let
                   _v = Lens.Family2.view (Data.ProtoLens.Field.field @"label") _x
                 in
                   if (Prelude.==) _v Data.ProtoLens.fieldDefault then
                       Data.Monoid.mempty
                   else
                       (Data.Monoid.<>)
                         (Data.ProtoLens.Encoding.Bytes.putVarInt 18)
                         ((Prelude..)
                            (\ bs
                               -> (Data.Monoid.<>)
                                    (Data.ProtoLens.Encoding.Bytes.putVarInt
                                       (Prelude.fromIntegral (Data.ByteString.length bs)))
                                    (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                            Data.Text.Encoding.encodeUtf8
                            _v))
                (Data.ProtoLens.Encoding.Wire.buildFieldSet
                   (Lens.Family2.view Data.ProtoLens.unknownFields _x)))
instance Control.DeepSeq.NFData Batch where
  rnf
    = \ x__
        -> Control.DeepSeq.deepseq
             (_Batch'_unknownFields x__)
             (Control.DeepSeq.deepseq
                (_Batch'items x__) (Control.DeepSeq.deepseq (_Batch'label x__) ()))
{- | Fields :

         * 'Proto.Perf_Fields.id' @:: Lens' Item Data.Word.Word32@
         * 'Proto.Perf_Fields.name' @:: Lens' Item Data.Text.Text@
         * 'Proto.Perf_Fields.scores' @:: Lens' Item [Data.Int.Int32]@
         * 'Proto.Perf_Fields.vec'scores' @:: Lens' Item (Data.Vector.Unboxed.Vector Data.Int.Int32)@
         * 'Proto.Perf_Fields.payload' @:: Lens' Item Data.ByteString.ByteString@
         * 'Proto.Perf_Fields.meta' @:: Lens' Item Meta@
         * 'Proto.Perf_Fields.maybe'meta' @:: Lens' Item (Prelude.Maybe Meta)@
         * 'Proto.Perf_Fields.tags' @:: Lens' Item [Data.Text.Text]@
         * 'Proto.Perf_Fields.vec'tags' @:: Lens' Item (Data.Vector.Vector Data.Text.Text)@
         * 'Proto.Perf_Fields.note' @:: Lens' Item Data.Text.Text@ -}
data Item
  = Item'_constructor {_Item'id :: !Data.Word.Word32,
                       _Item'name :: !Data.Text.Text,
                       _Item'scores :: !(Data.Vector.Unboxed.Vector Data.Int.Int32),
                       _Item'payload :: !Data.ByteString.ByteString,
                       _Item'meta :: !(Prelude.Maybe Meta),
                       _Item'tags :: !(Data.Vector.Vector Data.Text.Text),
                       _Item'note :: !Data.Text.Text,
                       _Item'_unknownFields :: !Data.ProtoLens.FieldSet}
  deriving stock (Prelude.Eq, Prelude.Ord)
instance Prelude.Show Item where
  showsPrec _ __x __s
    = Prelude.showChar
        '{'
        (Prelude.showString
           (Data.ProtoLens.showMessageShort __x) (Prelude.showChar '}' __s))
instance Data.ProtoLens.Field.HasField Item "id" Data.Word.Word32 where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'id (\ x__ y__ -> x__ {_Item'id = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Item "name" Data.Text.Text where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'name (\ x__ y__ -> x__ {_Item'name = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Item "scores" [Data.Int.Int32] where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'scores (\ x__ y__ -> x__ {_Item'scores = y__}))
        (Lens.Family2.Unchecked.lens
           Data.Vector.Generic.toList
           (\ _ y__ -> Data.Vector.Generic.fromList y__))
instance Data.ProtoLens.Field.HasField Item "vec'scores" (Data.Vector.Unboxed.Vector Data.Int.Int32) where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'scores (\ x__ y__ -> x__ {_Item'scores = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Item "payload" Data.ByteString.ByteString where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'payload (\ x__ y__ -> x__ {_Item'payload = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Item "meta" Meta where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'meta (\ x__ y__ -> x__ {_Item'meta = y__}))
        (Data.ProtoLens.maybeLens Data.ProtoLens.defMessage)
instance Data.ProtoLens.Field.HasField Item "maybe'meta" (Prelude.Maybe Meta) where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'meta (\ x__ y__ -> x__ {_Item'meta = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Item "tags" [Data.Text.Text] where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'tags (\ x__ y__ -> x__ {_Item'tags = y__}))
        (Lens.Family2.Unchecked.lens
           Data.Vector.Generic.toList
           (\ _ y__ -> Data.Vector.Generic.fromList y__))
instance Data.ProtoLens.Field.HasField Item "vec'tags" (Data.Vector.Vector Data.Text.Text) where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'tags (\ x__ y__ -> x__ {_Item'tags = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Item "note" Data.Text.Text where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Item'note (\ x__ y__ -> x__ {_Item'note = y__}))
        Prelude.id
instance Data.ProtoLens.Message Item where
  messageName _ = Data.Text.pack "bench.perf.Item"
  packedMessageDescriptor _
    = "\n\
      \\EOTItem\DC2\SO\n\
      \\STXid\CAN\SOH \SOH(\rR\STXid\DC2\DC2\n\
      \\EOTname\CAN\STX \SOH(\tR\EOTname\DC2\SYN\n\
      \\ACKscores\CAN\ETX \ETX(\ENQR\ACKscores\DC2\CAN\n\
      \\apayload\CAN\EOT \SOH(\fR\apayload\DC2$\n\
      \\EOTmeta\CAN\ENQ \SOH(\v2\DLE.bench.perf.MetaR\EOTmeta\DC2\DC2\n\
      \\EOTtags\CAN\ACK \ETX(\tR\EOTtags\DC2\DC2\n\
      \\EOTnote\CAN\a \SOH(\tR\EOTnote"
  packedFileDescriptor _ = packedFileDescriptor
  fieldsByTag
    = let
        id__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "id"
              (Data.ProtoLens.ScalarField Data.ProtoLens.UInt32Field ::
                 Data.ProtoLens.FieldTypeDescriptor Data.Word.Word32)
              (Data.ProtoLens.PlainField
                 Data.ProtoLens.Optional (Data.ProtoLens.Field.field @"id")) ::
              Data.ProtoLens.FieldDescriptor Item
        name__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "name"
              (Data.ProtoLens.ScalarField Data.ProtoLens.StringField ::
                 Data.ProtoLens.FieldTypeDescriptor Data.Text.Text)
              (Data.ProtoLens.PlainField
                 Data.ProtoLens.Optional (Data.ProtoLens.Field.field @"name")) ::
              Data.ProtoLens.FieldDescriptor Item
        scores__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "scores"
              (Data.ProtoLens.ScalarField Data.ProtoLens.Int32Field ::
                 Data.ProtoLens.FieldTypeDescriptor Data.Int.Int32)
              (Data.ProtoLens.RepeatedField
                 Data.ProtoLens.Packed (Data.ProtoLens.Field.field @"scores")) ::
              Data.ProtoLens.FieldDescriptor Item
        payload__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "payload"
              (Data.ProtoLens.ScalarField Data.ProtoLens.BytesField ::
                 Data.ProtoLens.FieldTypeDescriptor Data.ByteString.ByteString)
              (Data.ProtoLens.PlainField
                 Data.ProtoLens.Optional (Data.ProtoLens.Field.field @"payload")) ::
              Data.ProtoLens.FieldDescriptor Item
        meta__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "meta"
              (Data.ProtoLens.MessageField Data.ProtoLens.MessageType ::
                 Data.ProtoLens.FieldTypeDescriptor Meta)
              (Data.ProtoLens.OptionalField
                 (Data.ProtoLens.Field.field @"maybe'meta")) ::
              Data.ProtoLens.FieldDescriptor Item
        tags__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "tags"
              (Data.ProtoLens.ScalarField Data.ProtoLens.StringField ::
                 Data.ProtoLens.FieldTypeDescriptor Data.Text.Text)
              (Data.ProtoLens.RepeatedField
                 Data.ProtoLens.Unpacked (Data.ProtoLens.Field.field @"tags")) ::
              Data.ProtoLens.FieldDescriptor Item
        note__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "note"
              (Data.ProtoLens.ScalarField Data.ProtoLens.StringField ::
                 Data.ProtoLens.FieldTypeDescriptor Data.Text.Text)
              (Data.ProtoLens.PlainField
                 Data.ProtoLens.Optional (Data.ProtoLens.Field.field @"note")) ::
              Data.ProtoLens.FieldDescriptor Item
      in
        Data.Map.fromList
          [(Data.ProtoLens.Tag 1, id__field_descriptor),
           (Data.ProtoLens.Tag 2, name__field_descriptor),
           (Data.ProtoLens.Tag 3, scores__field_descriptor),
           (Data.ProtoLens.Tag 4, payload__field_descriptor),
           (Data.ProtoLens.Tag 5, meta__field_descriptor),
           (Data.ProtoLens.Tag 6, tags__field_descriptor),
           (Data.ProtoLens.Tag 7, note__field_descriptor)]
  unknownFields
    = Lens.Family2.Unchecked.lens
        _Item'_unknownFields
        (\ x__ y__ -> x__ {_Item'_unknownFields = y__})
  defMessage
    = Item'_constructor
        {_Item'id = Data.ProtoLens.fieldDefault,
         _Item'name = Data.ProtoLens.fieldDefault,
         _Item'scores = Data.Vector.Generic.empty,
         _Item'payload = Data.ProtoLens.fieldDefault,
         _Item'meta = Prelude.Nothing,
         _Item'tags = Data.Vector.Generic.empty,
         _Item'note = Data.ProtoLens.fieldDefault,
         _Item'_unknownFields = []}
  parseMessage
    = let
        loop ::
          Item
          -> Data.ProtoLens.Encoding.Growing.Growing Data.Vector.Unboxed.Vector Data.ProtoLens.Encoding.Growing.RealWorld Data.Int.Int32
             -> Data.ProtoLens.Encoding.Growing.Growing Data.Vector.Vector Data.ProtoLens.Encoding.Growing.RealWorld Data.Text.Text
                -> Data.ProtoLens.Encoding.Bytes.Parser Item
        loop x mutable'scores mutable'tags
          = do end <- Data.ProtoLens.Encoding.Bytes.atEnd
               if end then
                   do frozen'scores <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                         (Data.ProtoLens.Encoding.Growing.unsafeFreeze
                                            mutable'scores)
                      frozen'tags <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                       (Data.ProtoLens.Encoding.Growing.unsafeFreeze mutable'tags)
                      (let missing = []
                       in
                         if Prelude.null missing then
                             Prelude.return ()
                         else
                             Prelude.fail
                               ((Prelude.++)
                                  "Missing required fields: "
                                  (Prelude.show (missing :: [Prelude.String]))))
                      Prelude.return
                        (Lens.Family2.over
                           Data.ProtoLens.unknownFields
                           (\ !t -> Prelude.reverse t)
                           (Lens.Family2.set
                              (Data.ProtoLens.Field.field @"vec'scores")
                              frozen'scores
                              (Lens.Family2.set
                                 (Data.ProtoLens.Field.field @"vec'tags") frozen'tags x)))
               else
                   do tag <- Data.ProtoLens.Encoding.Bytes.getVarInt
                      case tag of
                        8 -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       (Prelude.fmap
                                          Prelude.fromIntegral
                                          Data.ProtoLens.Encoding.Bytes.getVarInt)
                                       "id"
                                loop
                                  (Lens.Family2.set (Data.ProtoLens.Field.field @"id") y x)
                                  mutable'scores
                                  mutable'tags
                        18
                          -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       (do value <- do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                                       Data.ProtoLens.Encoding.Bytes.getBytes
                                                         (Prelude.fromIntegral len)
                                           Data.ProtoLens.Encoding.Bytes.runEither
                                             (case Data.Text.Encoding.decodeUtf8' value of
                                                (Prelude.Left err)
                                                  -> Prelude.Left (Prelude.show err)
                                                (Prelude.Right r) -> Prelude.Right r))
                                       "name"
                                loop
                                  (Lens.Family2.set (Data.ProtoLens.Field.field @"name") y x)
                                  mutable'scores
                                  mutable'tags
                        24
                          -> do !y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                        (Prelude.fmap
                                           Prelude.fromIntegral
                                           Data.ProtoLens.Encoding.Bytes.getVarInt)
                                        "scores"
                                v <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                       (Data.ProtoLens.Encoding.Growing.append mutable'scores y)
                                loop x v mutable'tags
                        26
                          -> do y <- do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                        Data.ProtoLens.Encoding.Bytes.isolate
                                          (Prelude.fromIntegral len)
                                          ((let
                                              ploop qs
                                                = do packedEnd <- Data.ProtoLens.Encoding.Bytes.atEnd
                                                     if packedEnd then
                                                         Prelude.return qs
                                                     else
                                                         do !q <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                                                    (Prelude.fmap
                                                                       Prelude.fromIntegral
                                                                       Data.ProtoLens.Encoding.Bytes.getVarInt)
                                                                    "scores"
                                                            qs' <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                                                     (Data.ProtoLens.Encoding.Growing.append
                                                                        qs q)
                                                            ploop qs'
                                            in ploop)
                                             mutable'scores)
                                loop x y mutable'tags
                        34
                          -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       (do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                           Data.ProtoLens.Encoding.Bytes.getBytes
                                             (Prelude.fromIntegral len))
                                       "payload"
                                loop
                                  (Lens.Family2.set (Data.ProtoLens.Field.field @"payload") y x)
                                  mutable'scores
                                  mutable'tags
                        42
                          -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       (do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                           Data.ProtoLens.Encoding.Bytes.isolate
                                             (Prelude.fromIntegral len) Data.ProtoLens.parseMessage)
                                       "meta"
                                loop
                                  (Lens.Family2.set (Data.ProtoLens.Field.field @"meta") y x)
                                  mutable'scores
                                  mutable'tags
                        50
                          -> do !y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                        (do value <- do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                                        Data.ProtoLens.Encoding.Bytes.getBytes
                                                          (Prelude.fromIntegral len)
                                            Data.ProtoLens.Encoding.Bytes.runEither
                                              (case Data.Text.Encoding.decodeUtf8' value of
                                                 (Prelude.Left err)
                                                   -> Prelude.Left (Prelude.show err)
                                                 (Prelude.Right r) -> Prelude.Right r))
                                        "tags"
                                v <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                       (Data.ProtoLens.Encoding.Growing.append mutable'tags y)
                                loop x mutable'scores v
                        58
                          -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       (do value <- do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                                       Data.ProtoLens.Encoding.Bytes.getBytes
                                                         (Prelude.fromIntegral len)
                                           Data.ProtoLens.Encoding.Bytes.runEither
                                             (case Data.Text.Encoding.decodeUtf8' value of
                                                (Prelude.Left err)
                                                  -> Prelude.Left (Prelude.show err)
                                                (Prelude.Right r) -> Prelude.Right r))
                                       "note"
                                loop
                                  (Lens.Family2.set (Data.ProtoLens.Field.field @"note") y x)
                                  mutable'scores
                                  mutable'tags
                        wire
                          -> do !y <- Data.ProtoLens.Encoding.Wire.parseTaggedValueFromWire
                                        wire
                                loop
                                  (Lens.Family2.over
                                     Data.ProtoLens.unknownFields (\ !t -> (:) y t) x)
                                  mutable'scores
                                  mutable'tags
      in
        (Data.ProtoLens.Encoding.Bytes.<?>)
          (do mutable'scores <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                  Data.ProtoLens.Encoding.Growing.new
              mutable'tags <- Data.ProtoLens.Encoding.Parser.Unsafe.unsafeLiftIO
                                Data.ProtoLens.Encoding.Growing.new
              loop Data.ProtoLens.defMessage mutable'scores mutable'tags)
          "Item"
  buildMessage
    = \ _x
        -> (Data.Monoid.<>)
             (let _v = Lens.Family2.view (Data.ProtoLens.Field.field @"id") _x
              in
                if (Prelude.==) _v Data.ProtoLens.fieldDefault then
                    Data.Monoid.mempty
                else
                    (Data.Monoid.<>)
                      (Data.ProtoLens.Encoding.Bytes.putVarInt 8)
                      ((Prelude..)
                         Data.ProtoLens.Encoding.Bytes.putVarInt Prelude.fromIntegral _v))
             ((Data.Monoid.<>)
                (let _v = Lens.Family2.view (Data.ProtoLens.Field.field @"name") _x
                 in
                   if (Prelude.==) _v Data.ProtoLens.fieldDefault then
                       Data.Monoid.mempty
                   else
                       (Data.Monoid.<>)
                         (Data.ProtoLens.Encoding.Bytes.putVarInt 18)
                         ((Prelude..)
                            (\ bs
                               -> (Data.Monoid.<>)
                                    (Data.ProtoLens.Encoding.Bytes.putVarInt
                                       (Prelude.fromIntegral (Data.ByteString.length bs)))
                                    (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                            Data.Text.Encoding.encodeUtf8
                            _v))
                ((Data.Monoid.<>)
                   (let
                      p = Lens.Family2.view (Data.ProtoLens.Field.field @"vec'scores") _x
                    in
                      if Data.Vector.Generic.null p then
                          Data.Monoid.mempty
                      else
                          (Data.Monoid.<>)
                            (Data.ProtoLens.Encoding.Bytes.putVarInt 26)
                            ((\ bs
                                -> (Data.Monoid.<>)
                                     (Data.ProtoLens.Encoding.Bytes.putVarInt
                                        (Prelude.fromIntegral (Data.ByteString.length bs)))
                                     (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                               (Data.ProtoLens.Encoding.Bytes.runBuilder
                                  (Data.ProtoLens.Encoding.Bytes.foldMapBuilder
                                     ((Prelude..)
                                        Data.ProtoLens.Encoding.Bytes.putVarInt
                                        Prelude.fromIntegral)
                                     p))))
                   ((Data.Monoid.<>)
                      (let
                         _v = Lens.Family2.view (Data.ProtoLens.Field.field @"payload") _x
                       in
                         if (Prelude.==) _v Data.ProtoLens.fieldDefault then
                             Data.Monoid.mempty
                         else
                             (Data.Monoid.<>)
                               (Data.ProtoLens.Encoding.Bytes.putVarInt 34)
                               ((\ bs
                                   -> (Data.Monoid.<>)
                                        (Data.ProtoLens.Encoding.Bytes.putVarInt
                                           (Prelude.fromIntegral (Data.ByteString.length bs)))
                                        (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                                  _v))
                      ((Data.Monoid.<>)
                         (case
                              Lens.Family2.view (Data.ProtoLens.Field.field @"maybe'meta") _x
                          of
                            Prelude.Nothing -> Data.Monoid.mempty
                            (Prelude.Just _v)
                              -> (Data.Monoid.<>)
                                   (Data.ProtoLens.Encoding.Bytes.putVarInt 42)
                                   ((Prelude..)
                                      (\ bs
                                         -> (Data.Monoid.<>)
                                              (Data.ProtoLens.Encoding.Bytes.putVarInt
                                                 (Prelude.fromIntegral (Data.ByteString.length bs)))
                                              (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                                      Data.ProtoLens.encodeMessage
                                      _v))
                         ((Data.Monoid.<>)
                            (Data.ProtoLens.Encoding.Bytes.foldMapBuilder
                               (\ _v
                                  -> (Data.Monoid.<>)
                                       (Data.ProtoLens.Encoding.Bytes.putVarInt 50)
                                       ((Prelude..)
                                          (\ bs
                                             -> (Data.Monoid.<>)
                                                  (Data.ProtoLens.Encoding.Bytes.putVarInt
                                                     (Prelude.fromIntegral
                                                        (Data.ByteString.length bs)))
                                                  (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                                          Data.Text.Encoding.encodeUtf8
                                          _v))
                               (Lens.Family2.view (Data.ProtoLens.Field.field @"vec'tags") _x))
                            ((Data.Monoid.<>)
                               (let _v = Lens.Family2.view (Data.ProtoLens.Field.field @"note") _x
                                in
                                  if (Prelude.==) _v Data.ProtoLens.fieldDefault then
                                      Data.Monoid.mempty
                                  else
                                      (Data.Monoid.<>)
                                        (Data.ProtoLens.Encoding.Bytes.putVarInt 58)
                                        ((Prelude..)
                                           (\ bs
                                              -> (Data.Monoid.<>)
                                                   (Data.ProtoLens.Encoding.Bytes.putVarInt
                                                      (Prelude.fromIntegral
                                                         (Data.ByteString.length bs)))
                                                   (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                                           Data.Text.Encoding.encodeUtf8
                                           _v))
                               (Data.ProtoLens.Encoding.Wire.buildFieldSet
                                  (Lens.Family2.view Data.ProtoLens.unknownFields _x))))))))
instance Control.DeepSeq.NFData Item where
  rnf
    = \ x__
        -> Control.DeepSeq.deepseq
             (_Item'_unknownFields x__)
             (Control.DeepSeq.deepseq
                (_Item'id x__)
                (Control.DeepSeq.deepseq
                   (_Item'name x__)
                   (Control.DeepSeq.deepseq
                      (_Item'scores x__)
                      (Control.DeepSeq.deepseq
                         (_Item'payload x__)
                         (Control.DeepSeq.deepseq
                            (_Item'meta x__)
                            (Control.DeepSeq.deepseq
                               (_Item'tags x__)
                               (Control.DeepSeq.deepseq (_Item'note x__) ())))))))
{- | Fields :

         * 'Proto.Perf_Fields.source' @:: Lens' Meta Data.Text.Text@
         * 'Proto.Perf_Fields.createdAt' @:: Lens' Meta Data.Word.Word64@
         * 'Proto.Perf_Fields.active' @:: Lens' Meta Prelude.Bool@ -}
data Meta
  = Meta'_constructor {_Meta'source :: !Data.Text.Text,
                       _Meta'createdAt :: !Data.Word.Word64,
                       _Meta'active :: !Prelude.Bool,
                       _Meta'_unknownFields :: !Data.ProtoLens.FieldSet}
  deriving stock (Prelude.Eq, Prelude.Ord)
instance Prelude.Show Meta where
  showsPrec _ __x __s
    = Prelude.showChar
        '{'
        (Prelude.showString
           (Data.ProtoLens.showMessageShort __x) (Prelude.showChar '}' __s))
instance Data.ProtoLens.Field.HasField Meta "source" Data.Text.Text where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Meta'source (\ x__ y__ -> x__ {_Meta'source = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Meta "createdAt" Data.Word.Word64 where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Meta'createdAt (\ x__ y__ -> x__ {_Meta'createdAt = y__}))
        Prelude.id
instance Data.ProtoLens.Field.HasField Meta "active" Prelude.Bool where
  fieldOf _
    = (Prelude..)
        (Lens.Family2.Unchecked.lens
           _Meta'active (\ x__ y__ -> x__ {_Meta'active = y__}))
        Prelude.id
instance Data.ProtoLens.Message Meta where
  messageName _ = Data.Text.pack "bench.perf.Meta"
  packedMessageDescriptor _
    = "\n\
      \\EOTMeta\DC2\SYN\n\
      \\ACKsource\CAN\SOH \SOH(\tR\ACKsource\DC2\GS\n\
      \\n\
      \created_at\CAN\STX \SOH(\EOTR\tcreatedAt\DC2\SYN\n\
      \\ACKactive\CAN\ETX \SOH(\bR\ACKactive"
  packedFileDescriptor _ = packedFileDescriptor
  fieldsByTag
    = let
        source__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "source"
              (Data.ProtoLens.ScalarField Data.ProtoLens.StringField ::
                 Data.ProtoLens.FieldTypeDescriptor Data.Text.Text)
              (Data.ProtoLens.PlainField
                 Data.ProtoLens.Optional (Data.ProtoLens.Field.field @"source")) ::
              Data.ProtoLens.FieldDescriptor Meta
        createdAt__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "created_at"
              (Data.ProtoLens.ScalarField Data.ProtoLens.UInt64Field ::
                 Data.ProtoLens.FieldTypeDescriptor Data.Word.Word64)
              (Data.ProtoLens.PlainField
                 Data.ProtoLens.Optional
                 (Data.ProtoLens.Field.field @"createdAt")) ::
              Data.ProtoLens.FieldDescriptor Meta
        active__field_descriptor
          = Data.ProtoLens.FieldDescriptor
              "active"
              (Data.ProtoLens.ScalarField Data.ProtoLens.BoolField ::
                 Data.ProtoLens.FieldTypeDescriptor Prelude.Bool)
              (Data.ProtoLens.PlainField
                 Data.ProtoLens.Optional (Data.ProtoLens.Field.field @"active")) ::
              Data.ProtoLens.FieldDescriptor Meta
      in
        Data.Map.fromList
          [(Data.ProtoLens.Tag 1, source__field_descriptor),
           (Data.ProtoLens.Tag 2, createdAt__field_descriptor),
           (Data.ProtoLens.Tag 3, active__field_descriptor)]
  unknownFields
    = Lens.Family2.Unchecked.lens
        _Meta'_unknownFields
        (\ x__ y__ -> x__ {_Meta'_unknownFields = y__})
  defMessage
    = Meta'_constructor
        {_Meta'source = Data.ProtoLens.fieldDefault,
         _Meta'createdAt = Data.ProtoLens.fieldDefault,
         _Meta'active = Data.ProtoLens.fieldDefault,
         _Meta'_unknownFields = []}
  parseMessage
    = let
        loop :: Meta -> Data.ProtoLens.Encoding.Bytes.Parser Meta
        loop x
          = do end <- Data.ProtoLens.Encoding.Bytes.atEnd
               if end then
                   do (let missing = []
                       in
                         if Prelude.null missing then
                             Prelude.return ()
                         else
                             Prelude.fail
                               ((Prelude.++)
                                  "Missing required fields: "
                                  (Prelude.show (missing :: [Prelude.String]))))
                      Prelude.return
                        (Lens.Family2.over
                           Data.ProtoLens.unknownFields (\ !t -> Prelude.reverse t) x)
               else
                   do tag <- Data.ProtoLens.Encoding.Bytes.getVarInt
                      case tag of
                        10
                          -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       (do value <- do len <- Data.ProtoLens.Encoding.Bytes.getVarInt
                                                       Data.ProtoLens.Encoding.Bytes.getBytes
                                                         (Prelude.fromIntegral len)
                                           Data.ProtoLens.Encoding.Bytes.runEither
                                             (case Data.Text.Encoding.decodeUtf8' value of
                                                (Prelude.Left err)
                                                  -> Prelude.Left (Prelude.show err)
                                                (Prelude.Right r) -> Prelude.Right r))
                                       "source"
                                loop (Lens.Family2.set (Data.ProtoLens.Field.field @"source") y x)
                        16
                          -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       Data.ProtoLens.Encoding.Bytes.getVarInt "created_at"
                                loop
                                  (Lens.Family2.set (Data.ProtoLens.Field.field @"createdAt") y x)
                        24
                          -> do y <- (Data.ProtoLens.Encoding.Bytes.<?>)
                                       (Prelude.fmap
                                          ((Prelude./=) 0) Data.ProtoLens.Encoding.Bytes.getVarInt)
                                       "active"
                                loop (Lens.Family2.set (Data.ProtoLens.Field.field @"active") y x)
                        wire
                          -> do !y <- Data.ProtoLens.Encoding.Wire.parseTaggedValueFromWire
                                        wire
                                loop
                                  (Lens.Family2.over
                                     Data.ProtoLens.unknownFields (\ !t -> (:) y t) x)
      in
        (Data.ProtoLens.Encoding.Bytes.<?>)
          (do loop Data.ProtoLens.defMessage) "Meta"
  buildMessage
    = \ _x
        -> (Data.Monoid.<>)
             (let
                _v = Lens.Family2.view (Data.ProtoLens.Field.field @"source") _x
              in
                if (Prelude.==) _v Data.ProtoLens.fieldDefault then
                    Data.Monoid.mempty
                else
                    (Data.Monoid.<>)
                      (Data.ProtoLens.Encoding.Bytes.putVarInt 10)
                      ((Prelude..)
                         (\ bs
                            -> (Data.Monoid.<>)
                                 (Data.ProtoLens.Encoding.Bytes.putVarInt
                                    (Prelude.fromIntegral (Data.ByteString.length bs)))
                                 (Data.ProtoLens.Encoding.Bytes.putBytes bs))
                         Data.Text.Encoding.encodeUtf8
                         _v))
             ((Data.Monoid.<>)
                (let
                   _v = Lens.Family2.view (Data.ProtoLens.Field.field @"createdAt") _x
                 in
                   if (Prelude.==) _v Data.ProtoLens.fieldDefault then
                       Data.Monoid.mempty
                   else
                       (Data.Monoid.<>)
                         (Data.ProtoLens.Encoding.Bytes.putVarInt 16)
                         (Data.ProtoLens.Encoding.Bytes.putVarInt _v))
                ((Data.Monoid.<>)
                   (let
                      _v = Lens.Family2.view (Data.ProtoLens.Field.field @"active") _x
                    in
                      if (Prelude.==) _v Data.ProtoLens.fieldDefault then
                          Data.Monoid.mempty
                      else
                          (Data.Monoid.<>)
                            (Data.ProtoLens.Encoding.Bytes.putVarInt 24)
                            ((Prelude..)
                               Data.ProtoLens.Encoding.Bytes.putVarInt
                               (\ b -> if b then 1 else 0)
                               _v))
                   (Data.ProtoLens.Encoding.Wire.buildFieldSet
                      (Lens.Family2.view Data.ProtoLens.unknownFields _x))))
instance Control.DeepSeq.NFData Meta where
  rnf
    = \ x__
        -> Control.DeepSeq.deepseq
             (_Meta'_unknownFields x__)
             (Control.DeepSeq.deepseq
                (_Meta'source x__)
                (Control.DeepSeq.deepseq
                   (_Meta'createdAt x__)
                   (Control.DeepSeq.deepseq (_Meta'active x__) ())))
packedFileDescriptor :: Data.ByteString.ByteString
packedFileDescriptor
  = "\n\
    \\n\
    \Perf.proto\DC2\n\
    \bench.perf\"U\n\
    \\EOTMeta\DC2\SYN\n\
    \\ACKsource\CAN\SOH \SOH(\tR\ACKsource\DC2\GS\n\
    \\n\
    \created_at\CAN\STX \SOH(\EOTR\tcreatedAt\DC2\SYN\n\
    \\ACKactive\CAN\ETX \SOH(\bR\ACKactive\"\170\SOH\n\
    \\EOTItem\DC2\SO\n\
    \\STXid\CAN\SOH \SOH(\rR\STXid\DC2\DC2\n\
    \\EOTname\CAN\STX \SOH(\tR\EOTname\DC2\SYN\n\
    \\ACKscores\CAN\ETX \ETX(\ENQR\ACKscores\DC2\CAN\n\
    \\apayload\CAN\EOT \SOH(\fR\apayload\DC2$\n\
    \\EOTmeta\CAN\ENQ \SOH(\v2\DLE.bench.perf.MetaR\EOTmeta\DC2\DC2\n\
    \\EOTtags\CAN\ACK \ETX(\tR\EOTtags\DC2\DC2\n\
    \\EOTnote\CAN\a \SOH(\tR\EOTnote\"E\n\
    \\ENQBatch\DC2&\n\
    \\ENQitems\CAN\SOH \ETX(\v2\DLE.bench.perf.ItemR\ENQitems\DC2\DC4\n\
    \\ENQlabel\CAN\STX \SOH(\tR\ENQlabelJ\162\ACK\n\
    \\ACK\DC2\EOT\NUL\NUL\ETB\SOH\n\
    \\b\n\
    \\SOH\f\DC2\ETX\NUL\NUL\DC2\n\
    \\b\n\
    \\SOH\STX\DC2\ETX\STX\NUL\DC3\n\
    \\n\
    \\n\
    \\STX\EOT\NUL\DC2\EOT\EOT\NUL\b\SOH\n\
    \\n\
    \\n\
    \\ETX\EOT\NUL\SOH\DC2\ETX\EOT\b\f\n\
    \\v\n\
    \\EOT\EOT\NUL\STX\NUL\DC2\ETX\ENQ\STX\DC4\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\NUL\ENQ\DC2\ETX\ENQ\STX\b\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\NUL\SOH\DC2\ETX\ENQ\t\SI\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\NUL\ETX\DC2\ETX\ENQ\DC2\DC3\n\
    \\v\n\
    \\EOT\EOT\NUL\STX\SOH\DC2\ETX\ACK\STX\CAN\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\SOH\ENQ\DC2\ETX\ACK\STX\b\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\SOH\SOH\DC2\ETX\ACK\t\DC3\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\SOH\ETX\DC2\ETX\ACK\SYN\ETB\n\
    \\v\n\
    \\EOT\EOT\NUL\STX\STX\DC2\ETX\a\STX\DC2\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\STX\ENQ\DC2\ETX\a\STX\ACK\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\STX\SOH\DC2\ETX\a\a\r\n\
    \\f\n\
    \\ENQ\EOT\NUL\STX\STX\ETX\DC2\ETX\a\DLE\DC1\n\
    \\n\
    \\n\
    \\STX\EOT\SOH\DC2\EOT\n\
    \\NUL\DC2\SOH\n\
    \\n\
    \\n\
    \\ETX\EOT\SOH\SOH\DC2\ETX\n\
    \\b\f\n\
    \\v\n\
    \\EOT\EOT\SOH\STX\NUL\DC2\ETX\v\STX\DLE\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\NUL\ENQ\DC2\ETX\v\STX\b\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\NUL\SOH\DC2\ETX\v\t\v\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\NUL\ETX\DC2\ETX\v\SO\SI\n\
    \\v\n\
    \\EOT\EOT\SOH\STX\SOH\DC2\ETX\f\STX\DC2\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\SOH\ENQ\DC2\ETX\f\STX\b\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\SOH\SOH\DC2\ETX\f\t\r\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\SOH\ETX\DC2\ETX\f\DLE\DC1\n\
    \\v\n\
    \\EOT\EOT\SOH\STX\STX\DC2\ETX\r\STX\FS\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\STX\EOT\DC2\ETX\r\STX\n\
    \\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\STX\ENQ\DC2\ETX\r\v\DLE\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\STX\SOH\DC2\ETX\r\DC1\ETB\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\STX\ETX\DC2\ETX\r\SUB\ESC\n\
    \\v\n\
    \\EOT\EOT\SOH\STX\ETX\DC2\ETX\SO\STX\DC4\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ETX\ENQ\DC2\ETX\SO\STX\a\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ETX\SOH\DC2\ETX\SO\b\SI\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ETX\ETX\DC2\ETX\SO\DC2\DC3\n\
    \\v\n\
    \\EOT\EOT\SOH\STX\EOT\DC2\ETX\SI\STX\DLE\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\EOT\ACK\DC2\ETX\SI\STX\ACK\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\EOT\SOH\DC2\ETX\SI\a\v\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\EOT\ETX\DC2\ETX\SI\SO\SI\n\
    \\v\n\
    \\EOT\EOT\SOH\STX\ENQ\DC2\ETX\DLE\STX\ESC\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ENQ\EOT\DC2\ETX\DLE\STX\n\
    \\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ENQ\ENQ\DC2\ETX\DLE\v\DC1\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ENQ\SOH\DC2\ETX\DLE\DC2\SYN\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ENQ\ETX\DC2\ETX\DLE\EM\SUB\n\
    \\v\n\
    \\EOT\EOT\SOH\STX\ACK\DC2\ETX\DC1\STX\DC2\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ACK\ENQ\DC2\ETX\DC1\STX\b\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ACK\SOH\DC2\ETX\DC1\t\r\n\
    \\f\n\
    \\ENQ\EOT\SOH\STX\ACK\ETX\DC2\ETX\DC1\DLE\DC1\n\
    \\n\
    \\n\
    \\STX\EOT\STX\DC2\EOT\DC4\NUL\ETB\SOH\n\
    \\n\
    \\n\
    \\ETX\EOT\STX\SOH\DC2\ETX\DC4\b\r\n\
    \\v\n\
    \\EOT\EOT\STX\STX\NUL\DC2\ETX\NAK\STX\SUB\n\
    \\f\n\
    \\ENQ\EOT\STX\STX\NUL\EOT\DC2\ETX\NAK\STX\n\
    \\n\
    \\f\n\
    \\ENQ\EOT\STX\STX\NUL\ACK\DC2\ETX\NAK\v\SI\n\
    \\f\n\
    \\ENQ\EOT\STX\STX\NUL\SOH\DC2\ETX\NAK\DLE\NAK\n\
    \\f\n\
    \\ENQ\EOT\STX\STX\NUL\ETX\DC2\ETX\NAK\CAN\EM\n\
    \\v\n\
    \\EOT\EOT\STX\STX\SOH\DC2\ETX\SYN\STX\DC3\n\
    \\f\n\
    \\ENQ\EOT\STX\STX\SOH\ENQ\DC2\ETX\SYN\STX\b\n\
    \\f\n\
    \\ENQ\EOT\STX\STX\SOH\SOH\DC2\ETX\SYN\t\SO\n\
    \\f\n\
    \\ENQ\EOT\STX\STX\SOH\ETX\DC2\ETX\SYN\DC1\DC2b\ACKproto3"

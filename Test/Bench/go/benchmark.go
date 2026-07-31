package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"time"

	benchperf "protobuf-lean-benchmark/generated"

	"google.golang.org/protobuf/proto"
)

var protobufVersion = "unknown"

const (
	fnvOffset uint64 = 14695981039346656037
	fnvPrime  uint64 = 1099511628211
)

type result struct {
	dataSetupNS  uint64
	inputSetupNS uint64
	firstNS      uint64
	steadyNS     uint64
	outputBytes  uint64
	contentHash  uint64
	outputHash   uint64
	checksum     uint64
}

func hashByte(hash uint64, value byte) uint64 {
	return (hash ^ uint64(value)) * fnvPrime
}

func hashU64(hash, value uint64) uint64 {
	for range 8 {
		hash = hashByte(hash, byte(value))
		value >>= 8
	}
	return hash
}

func hashBytesWithLength(hash uint64, bytes []byte) uint64 {
	hash = hashU64(hash, uint64(len(bytes)))
	for _, value := range bytes {
		hash = hashByte(hash, value)
	}
	return hash
}

func hashBytes(bytes []byte) uint64 {
	hash := fnvOffset
	for _, value := range bytes {
		hash = hashByte(hash, value)
	}
	return hash
}

func contentHash(batch *benchperf.Batch) uint64 {
	hash := hashBytesWithLength(fnvOffset, []byte(batch.GetLabel()))
	hash = hashU64(hash, uint64(len(batch.GetItems())))
	for _, item := range batch.GetItems() {
		hash = hashU64(hash, uint64(item.GetId()))
		hash = hashBytesWithLength(hash, []byte(item.GetName()))
		hash = hashU64(hash, uint64(len(item.GetScores())))
		for _, score := range item.GetScores() {
			hash = hashU64(hash, uint64(uint32(score)))
		}
		hash = hashBytesWithLength(hash, item.GetPayload())
		if metadata := item.GetMeta(); metadata != nil {
			hash = hashByte(hash, 1)
			hash = hashBytesWithLength(hash, []byte(metadata.GetSource()))
			hash = hashU64(hash, metadata.GetCreatedAt())
			if metadata.GetActive() {
				hash = hashByte(hash, 1)
			} else {
				hash = hashByte(hash, 0)
			}
		} else {
			hash = hashByte(hash, 0)
		}
		hash = hashU64(hash, uint64(len(item.GetTags())))
		for _, tag := range item.GetTags() {
			hash = hashBytesWithLength(hash, []byte(tag))
		}
		hash = hashBytesWithLength(hash, []byte(item.GetNote()))
	}
	return hash
}

func makeBatch(count uint64) (*benchperf.Batch, error) {
	if count > uint64(^uint(0)>>1) {
		return nil, fmt.Errorf("item count is too large for the Go runtime")
	}
	batch := &benchperf.Batch{
		Label: fmt.Sprintf("batch-%d", count),
		Items: make([]*benchperf.Item, 0, int(count)),
	}
	for i := uint64(0); i < count; i++ {
		payload := make([]byte, 48+i%16)
		for j := range payload {
			payload[j] = byte((i*31 + uint64(j)*17 + 13) % 251)
		}
		item := &benchperf.Item{
			Id:   uint32(i),
			Name: fmt.Sprintf("item-%d", i),
			Scores: []int32{
				int32((i+1)*3 - 19), int32((i+1)*4 - 19),
				int32((i+1)*5 - 19), int32((i+1)*6 - 19),
				int32((i+1)*7 - 19), int32((i+1)*8 - 19),
				int32((i+1)*9 - 19), int32((i+1)*10 - 19),
			},
			Payload: payload,
			Meta: &benchperf.Meta{
				Source:    fmt.Sprintf("source-%d", i%11),
				CreatedAt: 1700000000 + i*17,
				Active:    i%2 == 0,
			},
			Tags: []string{
				fmt.Sprintf("tag-%d", i%5),
				fmt.Sprintf("group-%d", i%9),
				fmt.Sprintf("bucket-%d", i%13),
				fmt.Sprintf("region-%d", i%7),
			},
			Note: fmt.Sprintf("note-%d-%d", i%17, i*3),
		}
		batch.Items = append(batch.Items, item)
	}
	return batch, nil
}

func encode(batch *benchperf.Batch) ([]byte, error) {
	return proto.Marshal(batch)
}

func decode(bytes []byte) (*benchperf.Batch, error) {
	batch := &benchperf.Batch{}
	if err := proto.Unmarshal(bytes, batch); err != nil {
		return nil, err
	}
	return batch, nil
}

func consumeBytes(bytes []byte) uint64 {
	if len(bytes) == 0 {
		return 0
	}
	return uint64(len(bytes)) + uint64(bytes[0]) + uint64(bytes[len(bytes)-1])
}

func consumeBatch(batch *benchperf.Batch) uint64 {
	items := batch.GetItems()
	if len(items) == 0 {
		return uint64(len(batch.GetLabel()))
	}
	return uint64(len(items)) + uint64(items[0].GetId()) +
		uint64(items[len(items)-1].GetId()) + uint64(len(batch.GetLabel()))
}

func elapsedNS(start, stop time.Time) uint64 {
	return uint64(stop.Sub(start).Nanoseconds())
}

func runEncode(items, iterations uint64, validate bool) (result, error) {
	var output result
	start := time.Now()
	batch, err := makeBatch(items)
	if err != nil {
		return output, err
	}
	output.dataSetupNS = elapsedNS(start, time.Now())
	output.contentHash = contentHash(batch)

	start = time.Now()
	last, err := encode(batch)
	if err != nil {
		return output, err
	}
	output.firstNS = elapsedNS(start, time.Now())
	output.checksum = consumeBytes(last)

	start = time.Now()
	for range iterations {
		bytes, err := encode(batch)
		if err != nil {
			return output, err
		}
		output.checksum += consumeBytes(bytes)
		last = bytes
	}
	output.steadyNS = elapsedNS(start, time.Now())
	if validate {
		decoded, err := decode(last)
		if err != nil {
			return output, err
		}
		if actual := contentHash(decoded); actual != output.contentHash {
			return output, fmt.Errorf("go-binary encode content mismatch: expected %d, got %d", output.contentHash, actual)
		}
	}
	output.outputBytes = uint64(len(last))
	output.outputHash = hashBytes(last)
	return output, nil
}

func runDecode(items, iterations uint64, validate bool) (result, error) {
	var output result
	start := time.Now()
	batch, err := makeBatch(items)
	if err != nil {
		return output, err
	}
	output.dataSetupNS = elapsedNS(start, time.Now())
	output.contentHash = contentHash(batch)

	start = time.Now()
	input, err := encode(batch)
	if err != nil {
		return output, err
	}
	output.inputSetupNS = elapsedNS(start, time.Now())

	start = time.Now()
	last, err := decode(input)
	if err != nil {
		return output, err
	}
	output.firstNS = elapsedNS(start, time.Now())
	output.checksum = consumeBatch(last)

	start = time.Now()
	for range iterations {
		decoded, err := decode(input)
		if err != nil {
			return output, err
		}
		output.checksum += consumeBatch(decoded)
		last = decoded
	}
	output.steadyNS = elapsedNS(start, time.Now())
	if validate {
		if actual := contentHash(last); actual != output.contentHash {
			return output, fmt.Errorf("go-binary decode content mismatch: expected %d, got %d", output.contentHash, actual)
		}
	}
	output.outputBytes = uint64(len(input))
	output.outputHash = hashBytes(input)
	return output, nil
}

func parseU64(name, value string) (uint64, error) {
	parsed, err := strconv.ParseUint(value, 10, 64)
	if err != nil {
		return 0, fmt.Errorf("invalid %s: %w", name, err)
	}
	return parsed, nil
}

func printResult(operation string, items, iterations uint64, validate bool, value result) {
	perOperation := uint64(0)
	if iterations != 0 {
		perOperation = value.steadyNS / iterations
	}
	validation := 0
	if validate {
		validation = 1
	}
	fmt.Printf("BENCH_RESULT implementation=go-binary operation=%s items=%d iterations=%d data_setup_ns=%d input_setup_ns=%d first_ns=%d steady_ns=%d steady_ns_per_op=%d output_bytes=%d content_hash=%d output_hash=%d checksum=%d validation=%d runtime_version=%s protobuf_version=%s\n",
		operation, items, iterations, value.dataSetupNS, value.inputSetupNS,
		value.firstNS, value.steadyNS, perOperation, value.outputBytes,
		value.contentHash, value.outputHash, value.checksum, validation,
		runtime.Version(), protobufVersion)
}

func main() {
	if len(os.Args) == 2 && os.Args[1] == "startup" {
		fmt.Printf("BENCH_RESULT implementation=go-runtime operation=startup items=0 iterations=0 data_setup_ns=0 input_setup_ns=0 first_ns=0 steady_ns=0 steady_ns_per_op=0 output_bytes=0 content_hash=0 output_hash=0 checksum=0 validation=0 runtime_version=%s protobuf_version=%s\n", runtime.Version(), protobufVersion)
		return
	}
	if len(os.Args) == 2 && os.Args[1] == "version" {
		fmt.Printf("%s %s\n", protobufVersion, runtime.Version())
		return
	}
	if len(os.Args) != 5 {
		fmt.Fprintln(os.Stderr, "usage: <encode|decode> <items> <steady-iterations> <validate:0|1>")
		os.Exit(2)
	}
	operation := os.Args[1]
	items, err := parseU64("items", os.Args[2])
	if err != nil {
		fmt.Fprintln(os.Stderr, "benchmark error:", err)
		os.Exit(2)
	}
	iterations, err := parseU64("steady-iterations", os.Args[3])
	if err != nil {
		fmt.Fprintln(os.Stderr, "benchmark error:", err)
		os.Exit(2)
	}
	validation, err := parseU64("validate", os.Args[4])
	if err != nil || validation > 1 {
		fmt.Fprintln(os.Stderr, "benchmark error: validate must be 0 or 1")
		os.Exit(2)
	}
	validate := validation == 1
	var output result
	if operation == "encode" {
		output, err = runEncode(items, iterations, validate)
	} else if operation == "decode" {
		output, err = runDecode(items, iterations, validate)
	} else {
		err = fmt.Errorf("operation must be encode or decode")
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "benchmark error:", err)
		os.Exit(2)
	}
	printResult(operation, items, iterations, validate, output)
}

# The map: where bytes and calls come in to gosh

For REQ1/MAP-1. Each row is a place where gosh takes something from outside itself, with the file
and function that first reads it, who can send it, and whether it is proved, assumed, or not yet.

**How this was made, and how far to believe it.** By Claude Fable 5.2 on 2026-11-18, from gosh at
commit `d0cfd4f`: every part's README, the design's "What crosses a process or a machine" and
"ssh, gosh's trust" (`docs/DESIGN_v2.md`, 3.2 and 3.4), and a search of `src/` for every `read`,
`recv`, `recvfrom`, `recvmsg`, `accept`, `getenv`, `fread` and `getline`. The functions marked
**(opened)** were read; the others are named from their declarations and their callers, and their
bodies were not read. Nothing was run. Line numbers are at that commit. A boundary this search does
not find (bytes that come in by a call the search did not name) is not here.

"Today" is what gosh's own READMEs say of its tests and fuzzers; it was not checked again here.

## A. From anyone on the Internet, before any key

These are reached by a datagram from a stranger. They matter most (REQ1/SHAPE-3).

| # | What comes in | Read by (gosh) | Today | State |
| - | ------------- | -------------- | ----- | ----- |
| A1 | a STUN answer, on an end's path-finding socket | `src/strong/pathfinding/stunanswer.h` `Strong::StunAnswer::parse_checked` (gosh's branch `strong/main`; on main it is still all in `stun.h` `stun_parse`), called through `stun_parse` at `finding.h:438` | fuzzed (`stun-fuzzer`), and under AddressSanitizer | **proved, from gosh's own text on that branch**: for every sequence of bytes, `parse` ends, reads nothing at or past its length, writes nothing outside its 16 bytes, and keeps nothing, IPv4 or IPv6, never an IPv6 address of one link alone. What it reads is a `Datagram`, a window on bytes (`subarray.h`). What its fuzzer tries of it is said of every datagram, in C++, and proved (`domains/gosh/proofs/StunAnswer.proof.cpp`). **Assumed:** that the bytes are there and stay, where `stun_parse` makes the window from the pointer and length it is given (weak code; listed by the lint). **Not proved:** `stun_parse`, the edge that makes a socket address of what was kept (20 lines, tested by gosh). **Not on gosh's main** |
| A2 | any datagram on that socket | `src/pathfinding/punch.cc:253` (`recvfrom`), then `finding.h:353` `PathFinding::receive` **(opened)**: the mark, then the one length a probe may have, before the cipher is called | fuzzed (`finding-fuzzer`); the length check is the fifth security fault mended | not yet |
| A3 | a message that claims to be from the meetup, at an end | `src/meetup/messages.h:198` `meetup_read_header` **(opened)**, by `finding.h:209` `from_meetup`; taken only from the meetup's address, which a sender can forge | unit tests; reached by `finding-fuzzer` | not yet |
| A4 | any datagram to a meetup: a public machine, a process that runs for months | `src/meetup/serve.cc:106` (`recvmsg`), then `src/strong/pathfinding/stunrequest.h` `Strong::is_stun_request_checked` **(opened)** and `stun_answer_to`, or `registrations.h:159` `Registrations::datagram`, which begins with `meetup_read_header` | fuzzed (`registrations-fuzzer`), held to a model of what it may answer | **`is_stun_request_checked` is proved, from gosh's own text**: it ends and reads nothing at or past the datagram's size. It takes a `Datagram`, made in `serve.cc` from the array `recvmsg` filled and the count it gave. **Assumed:** that the count is what was received (weak code; listed by the lint). **`meetup_read_header` is an edge over `Strong::MeetupHeader`, which is proved** (`src/strong/meetup/header.h`): for every datagram it ends and reads nothing outside it, and a head that is read says a ticket, an end and a sealed part that lie inside a datagram of that length (`domains/gosh/proofs/MeetupHeader.proof.cpp`, in C++). The edge's ten lines, which make pointers and text of those numbers, are read, not proved. `stun_answer_to`, the cipher (`meetup_open`) and `Registrations::datagram`: not yet |
| A5 | any datagram to the local relay's direct socket | `src/relay/local.cc:470`; not read: `whose.h:45` `same_udp_address` says whether it is the server's, and it is passed to the client | `tests/relay-spoof.py`, `whose-test` | not yet (little to prove: an address compared) |
| A6 | a session datagram, at the client or the server | the core's `Connection::recv`, then the cipher | mosh's | **assumed** (mosh's core, the cipher) |

## B. From whoever holds a key: the other end, or a ticket's holder

Reached only after the cipher has opened something. The sender is then the other end of the
session (a host that lies, or a client that does) or someone holding a meetup's ticket.

| # | What comes in | Read by (gosh) | Today | State |
| - | ------------- | -------------- | ----- | ----- |
| B1 | a side-channel payload, handed to its kind | the core's `Transport::recv` as changed by seam patch 03, then `src/forwarding/forwarding.h:88` `Forwarding::sidechannel_recv` | **not fuzzed** (forwarding's README says so) | not yet |
| B2 | a frame's 13-byte header, and its number | `src/forwarding/frame.cc` `decode_frame`, `ReplayWindow::accept` **(opened)** | fuzzed (`frame-fuzzer`) | not yet |
| B3 | a TCP segment as a datagram, and its options | `src/forwarding/tcp/tcpforward.cc:138`, `tcpinudp.cc` `TCPInUDP::from_datagram`, `options.h:30` `SegmentOptions::walk` **(opened)**, `held.h` (ranges the other end says it holds), then `connection.h` `Connections` (1,034 lines: gosh's TCP) | fuzzed (`tcpinudp-fuzzer`, `tcpadapter-fuzzer`) | not yet |
| B4 | a UDP forward's payload: a datagram or a fragment | `src/forwarding/udp/conversations.h:241` `Conversations::payload`, `receiving.h:77` `Receiving::fragment`, `fragments.cc` `Fragments::add` and `rebuild` | fuzzed (`udpforward-fuzzer`) | not yet |
| B5 | a copy's messages, from the other end of the stream | `src/copy/messages.h:153` `unframe`, its `Reader`, `read_list`, `read_want`, `read_begin`, `read_end`, `read_result`; `names.h:21` `safe_relative_path`; the edge is `filecopy.cc` (1,089 lines) | fuzzed (`filecopy-fuzzer`, `sender-fuzzer`); a lying end is tested | not yet |
| B6 | what is inside a sealed REGISTER or PASS, at the meetup | `src/meetup/messages.h:162` `meetup_read_register`, `:119` `meetup_addr_of`, and `src/strong/meetup/counterwindow.h` `Strong::CounterWindow::take` **(opened)** | the same fuzzer | **`CounterWindow` and `bounded` are proved, from gosh's own text on the branch `strong/main`** (not on main): a `MeetupCounter` is a `bounded` number from 0 to 2^62 - 1, proved once for every type and bounds; `take`, given one, ends, reads and writes nothing outside its sixteen words, makes no undefined shift, and keeps the highest counter taken at most 2^62 - 1, so its `top + 1` never passes the end of 64 bits. Not proved: that no counter is taken twice. `Registrations::datagram`, which is not proved, comes in by `take_checked` with a `MeetupCounterChecked`, which tests the number when the program runs: the process ends, saying which line made it, if it is not a counter. The check refuses gosh if code that is not proved makes a counter any other way. **Assumed:** that no datagram can make that test fail: `meetup_open` (`messages.h`) gives a nonce's low 62 bits and nothing else, and `datagram` reaches the test only when it has; read by a person, and if it were wrong, one datagram from a ticket's holder would end the meetup. **And what a message is sealed with is proved (2026-11-19):** `Strong::MeetupNonce` (`src/strong/meetup/nonce.h`), over which `meetup_seal` and `meetup_open` are edges. `proofs/MeetupNonce.proof.cpp` says, of every 64-bit nonce and of every sender and counter of 62 bits: reading and writing one lose nothing, either way; so the four senders under a ticket's key never make one nonce, and `meetup_open` gives a counter of 62 bits because the class's invariant says so, no longer because a person read a mask. Not proved: that a sender's counter is never used twice (each side starts it from the time of day: FINDINGS, 2026-11-19); the cipher; the edges' own lines. **And what a REGISTER says once opened is proved (2026-11-20):** `meetup_read_register` is an edge over `Strong::MeetupRegister` (`src/strong/meetup/register.h`, on gosh's branch `strong/register`), which takes the opened text as a `Strong::Opened`; for every text it ends, reads nothing outside it, keeps a family of 0, 4 or 6, and one other than 0 only from a text of 27 bytes (`proofs/MeetupRegister.proof.cpp`). Not proved: that the time kept is the text's last eight bytes, most significant first (the proof reader takes no such equation yet); the edge's lines, which copy where out. **And since 2026-11-21 (gosh `strong/fixed`)** it reads a `Strong::fixed<27, Register>`, a window of 27 bytes by its type, so that a text read had 27 bytes is the type, no longer a proof; `src/meetup/sealed.h` finds the length once, for every kind (read by a person). A TIME, at the end, is read the same way by `Strong::Meetup::Time` (`fixed<16, Time>`; proved: memory, ending, a counter kept is under 2^62). `meetup_addr_of`: not yet |
| B7 | what is inside a sealed REGISTERED or TIME, at an end | `src/meetup/messages.h:177` `meetup_read_time`, `:119` `meetup_addr_of` | `finding-test` | not yet |
| B8 | an opened probe: its number and direction | `src/pathfinding/finding.h:377` on, in `PathFinding::receive` **(opened)** | `finding-fuzzer` | not yet |
| B9 | the two fields gosh adds to mosh's instruction (what an end can do; loss) | protobuf, in the core, as changed by seam patches 01 and 02 | mosh's, and gosh's outside tests | **assumed** with the core, unless the owner says the seam's patches are gosh's to prove |

## C. Through ssh: the host, once ssh has said which host it is

| # | What comes in | Read by (gosh) | Today | State |
| - | ------------- | -------------- | ----- | ----- |
| C1 | the host's lines at login (`MOSH IP`, `MOSH CONNECT port key`) | `src/command/login.cc:164`, then `startup.cc` `startup_line` | `startup-test`, outside tests | not yet |
| C2 | the relay's stream, each way: two bytes of length and a datagram, and words | `src/relay/local.cc:478` and `remote.cc:109`, then `frame.h:53` `RelayFrameParser::next` **(opened)**, `frame.h:75` `relay_words_of`; the words go to `stun.h:112` `parse_ip_port` and `meetup/ticket.h:102` `parse_ticket` | fuzzed (`relay/frame-fuzzer`) | not yet |
| C3 | a ticket's text, fetched over ssh | `src/relay/local.cc:446`, then `parse_ticket` | `ticket-test` | not yet |
| C4 | what `ssh -G` prints of the user's configuration | `src/command/sshconfig.cc:9` `read_ssh_config` | `sshconfig-test` | not yet |
| C5 | the bytes of ssh's own connection, when gosh is its ProxyCommand | `src/command/proxy.cc:257` and `:265`: carried, not read | outside tests | not yet (carried only) |

## D. From this machine

| # | What comes in | Read by (gosh) | Who | State |
| - | ------------- | -------------- | --- | ----- |
| D1 | the words of a command line | `src/seam/options.h` `take_forward_options`, `which_role`, `operands`; `src/command/options.cc` `parse_options`; `src/forwarding/forward.cc:22` `ForwardSpec`; `src/copy/options.h:39` `parse`; `src/forwarding/stream/streamchild.h` `stream_words` with `src/seam/applications.h` `stream_words_valid` and `connect_port_valid` | the user; at the server, whatever the client's command wrote through ssh | not yet |
| D2 | the environment | `src/relay/settings.h:82` `relay_settings`, `:113` and `:118` (what ssh says of the connection); `src/seam/client-main.cc:80` and `:93`; `HOME`, `SHELL`, `PATH`, the locales, each read in one place | the user, or whatever started the program | not yet |
| D3 | the kernel's list of UDP sockets | `src/relay/local.cc:85`, then `whose.h:80` `udp_sender_is_users` | the kernel | not yet |
| D4 | a datagram to the local relay's loopback port | `src/relay/local.cc:457` | any user of this machine | not yet (carried; `whose.h` says whose) |
| D5 | a datagram to the remote relay, on the server's machine | `src/relay/remote.cc:188` and `:192`; `whose.h:141` `remote_ways_kept` | any user of that machine | not yet |
| D6 | what forwarded applications send: connections, bytes, datagrams | `src/forwarding/tcp/tcpadapter.cc:169` and `:225`, into `Connections::read`; `src/forwarding/udp/udpforward.cc:233` and `:256`, into `Conversations` | any program that can reach the forwarded port | not yet (carried: lengths and limits are what there is to prove) |
| D7 | what a stream's application reads and writes | `src/seam/applications.cc:104`, `:152`, `:160` | the user's own processes | not yet (carried) |
| D8 | files: what a copy finds at its destination; the meetup's master key | `src/copy/filecopy.cc`; `src/meetup/master.cc:105` | the file system; the receiving end follows a symbolic link already there (gosh's findings, 2026-11-13) | not yet; what a file system does is outside what the generator reads |
| D9 | the terminal's answer when asked its colours | `src/command/login.cc` | the terminal | not yet |

## E. Assumed

By the owner's word (2026-11-17): ssh, mosh's core, "which is exactly where we want it". With them,
as this project reads it *(inferred)*: the cipher (AES-OCB, in the core), protobuf, the kernel, and
the C and C++ libraries. That last one is larger than it sounds: see the second point below.

## What the map suggests

These are the agent's reading, for the owner to judge (REQ1/SHAPE-5: this project proposes).

1. **Six places take bytes from a stranger, and one of them has a proved model.** Of the other
   five, A6 is mosh's, A5 compares an address, and A2, A3 and A4 are where a proof would count most.
   A4 is the worst place for a flaw: a meetup has a public address and runs for months.
2. **Few of gosh's boundaries are domains in this project's sense.** A domain here is a class with
   all its state `private`. Most of gosh's readers are free functions that take `const char*` and a
   length, or a `std::string`, and give back a struct. The ones that are already classes with state
   of their own are `CounterWindow`, `ReplayWindow`, `RelayFrameParser`, `Fragments` and
   `Connections`. So either the generator learns to read a function that keeps no state, or each
   reader is written again as a class, as the STUN parser was.
3. **`std::string` is everywhere, and the generator does not read it.** Its bounds are the
   library's, so every model so far replaces it with a view of bytes. A proof of such a model says
   nothing of `.assign`, `.erase` or `[]` on the string in gosh's own code. Either the library is
   listed as assumed (it is, above, inferred), or gosh's readers move to a checked view of bytes.
4. **Almost every row in A and B calls the cipher before or after its own logic.** The generator
   refuses calls today (queue item 6), so the rows that can be proved now are the ones that only
   read bytes: `meetup_read_header`, `is_stun_request`, `SegmentOptions::walk`, `decode_frame`,
   and the two windows.
5. **What gosh proves by fuzzing a model against the code** (the meetup's fuzzer, held to
   "passed on no second time") is a statement of correctness, the second goal. An `invariant()`
   could say part of it.

## Which domain next

`CounterWindow` was recommended here and is done (2026-11-18; `docs/FINDINGS.md`): first as a
rewrite, then, once the generator had learned what its text needs, from gosh's own file.

The STUN reader and `is_stun_request` followed the same day, both from gosh's own text: the first
after gosh's code was reshaped on a `strong/` branch, the second with gosh unchanged.

Next, the agent recommends `meetup_read_header` (A3, A4), the rest of the meetup's front door. It
fills a struct that holds a `std::string` and a pointer into the datagram, so it is a reshaping of
gosh like the STUN reader's: a class that keeps the kind, the end, and where the sealed part
begins and ends, with the ticket's 16 bytes copied by an edge. The other choice is
`SegmentOptions::walk` (B3), which takes a function to call for each option: the generator reads
no such thing, so it too would be reshaped.

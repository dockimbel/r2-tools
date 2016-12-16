REBOL [
	Title: "PostgresQL Protocol"
    Author: "SOFTINNOV"
    Email: pgsql@softinnov.com
    Web: http://rebol.softinnov.org/pgsql/
    Date: 28/03/2011
    File: %pgsql-protocol.r
    Version: 0.9.1
    Purpose: "PostgresQL client protocol implementation for /Core"
    History: {
    	v0.9.1 - 28/03/2011
    		o added support for SEND-SQL and NAME-FIELDS public functions
    }
]

make root-protocol [

	scheme: 'pgSQL
    port-id: 5432
	port-flags: system/standard/port-flags/pass-thru or 32 ; /binary

	fast-query: none

	sys-copy: 	get in system/words 'copy
	sys-insert: get in system/words 'insert
	sys-pick: 	get in system/words 'pick
	sys-close: 	get in system/words 'close
	net-log: 	get in net-utils	'net-log	
	
	throws: [closed "closed"]
	
;------ Internals --------

	defs: [
		types [
			16		bool			[to logic! find ["t" "true" "y" "yes" "1"]]
			17		bytea			[to-rebol-binary]
			18		char			[to char!]
			19		name			none
			20		int8			[to decimal!]
			21		int2			[to integer!]
			23		int4			[to integer!]
			24		regproc			none
			25		text			none
			26		oid				[to integer!]
			27		tid				none
			28		xid				none
			29		cid				none
			32		SET				none
			210		smgr			none
			600		point 			none
			601		lseg			none
			602		path			none
			603		box				none
			604		polygon			none
			628		line			none
			650		cidr			none
			700		float4			[to decimal!]
			701		float8			[to decimal!]
			702		abstime			none
			703		reltime			none
			704		tinterval		none
			705		unknown			none
			718		circle			none
			790		money			[to money!]
			829		macaddr			none
			869		inet			[to-rebol-inet]
			1033	aclitem			none
			1042	bpchar			none
			1043	varchar			none
			1082	date			[try-to-date]
			1083	time			none
			1114	timestamp		none
			1184	timestamptz		none
			1186	interval		none
			1266	timetz			none
			1560	bit				none
			1562	varbit			none
			1700	numeric			none
			1790	refcursor		none
		]
	]

	locals-class: context [
	;--- Internals (do not touch!)---
		buf-size: 64 * 1024
		state:
		last-status:
		stream-end?:
		buffer:
		cancel-key: none
	;-------
		auto-commit: on		; not used, just reserved for /Command compatibility.
		rows: 10			; not used, just reserved for /Command compatibility.
		auto-conv?: on
		auto-ping?: off		; not yet supported
		flat?: off
		matched-rows:
		cursor:
		columns:
		;protocol:			
		;version:
		process-id:
		last-notice:
		error-code:
		error-msg:
		conv-list: none
	]

	column-class: context [name: length: type: flags: none]

	conv-model: make block! length? defs/types
	
;------ Type Conversion ------
	
	extract-conv-list: does [
		blk: defs/types
		forskip blk 3 [append conv-model sys-copy/deep reduce [blk/2 blk/3]]
	]
	
	set 'change-type-handler func [p [port!] type [word!] blk [block!]][
		head change/only next find p/locals/conv-list type blk
	]
	
	try-to-date: func [val][error? try [val: to-date val] val]
	
	to-rebol-inet: func [val][
		set [a b] parse val "/"
		either b [reduce [to tuple! a to integer! b]][to tuple! a]
	]
	
	special: charset [#"'" #"\"]
	digit: charset [#"0" - #"9"]
		
	to-rebol-binary: func [val /local out a b c][
		out: make binary! length? val
		parse/all val [
			some [
				#"\" [
					a: special (sys-insert tail out first a)
					| a: digit b: digit c: digit (
						sys-insert tail out to char! (a/1 - 48 * 8 + b/1 - 48 * 8 + c/1 - 48)
					)
				] | a: skip (sys-insert tail out first a)
			] | end
		]
		out
	]
		
	convert-types: func [p [port!] rows [block!] /local row i
		convert-body action cols col conv-func tmp
	][
		cols: p/locals/columns
		convert-body: make block! 1
		action: [if tmp: sys-pick row (i)]
		foreach col cols [
			i: index? find cols col
			if 'none <> conv-func: select p/locals/conv-list col/type [
				append convert-body append/only compose action head
					sys-insert at compose [change/only at row (i) :tmp] 5 conv-func
			]
		]
		if not empty? convert-body [
			either p/locals/flat? [
				while [not tail? rows][
					row: rows
					do convert-body
					rows: skip rows length? cols
				]
			][
				foreach row rows :convert-body
			]
		]
	]
	
	decode: func [int [integer!]][any [select defs/types int 'unknown]]

	printable: exclude charset [#" " - #"~"] charset [#"\" #"'"]
	
	to-octal: func [val][
		head sys-insert tail sys-copy "\\" reduce [
			first to string! to integer! val / 64
			first to string! to integer! (remainder val 64) / 8
			to string! remainder val 8
		]
	]
	
	sql-escape: func [value [string!] /local out mark][
		out: make string! 3 * length? value
		parse/all value [
			some [
				mark: [
					printable (sys-insert tail out first mark)
					| skip (sys-insert tail out to-octal to integer! first mark)
				]
			] | end
		]
		out
	]
	
	to-sql: func [value /local res][
		switch/default type?/word value [
			none!	["NULL"]
			date!	[
				rejoin ["'" value/year "-" value/month "-" value/day
					either value: value/time [
						rejoin [" " value/hour	":" value/minute ":" value/second]
					][""] "'"
				]
			]
			time!	[join "'" [value/hour ":" value/minute ":" value/second "'"]]
			money!	[to-sql form value]
			string!	[join "'" [sql-escape value "'"]]
			binary!	[to-sql to string! value]
			tuple!  [to-sql to string! value]
			pair!	[rejoin ["(" value/x "," value/y ")"]]
		][form value]
	]
	
	map-rebol-values: func [data [block!] /local args sql mark][
		args: reduce next data
		sql: sys-copy sys-pick data 1
		mark: sql
		while [found? mark: find mark #"?"][
			mark: sys-insert remove mark either tail? args ["NULL"][to-sql args/1]
			if not tail? args [args: next args]
		]
		net-log sql
		sql
	]

;------ Data reading ------

	int: int32: string: field: fields: len: col: msg: byte: bitmap: bytes: pos: sz: none

	read-byte:	[copy byte skip (byte: to integer! to char! :byte)]
	read-int:	[copy bytes 2 skip (int: to integer! to binary! bytes)]
	read-int32:	[copy bytes 4 skip (int32: to integer! to binary! bytes)]
	read-bytes:	[read-int32 (int32: int32 - sz) copy bytes [int32 skip]]
					
	read: func [[throw] port [port!] /local len][
		pl: port/locals
		if -1 = len: read-io port/sub-port pl/buffer pl/buf-size - length? pl/buffer [
			sys-close port/sub-port
			throw throws/closed
		]
		if positive? len [net-log ["low level read of " len "bytes"]]
		if negative? len [throw "IO error"]
		len
    ]
    
	read-stream: func [port [port!] /wait f-state [word!] /records rows /part count
		/local final complete msg pl pos stopped row stop error test-error test-exit a-data
	][
		pl: port/locals
		bind protocol-rules 'final
		final: f-state
		error: none
		test-error: [if error [pl/stream-end?: true make error! error]]
		test-exit: [
			all [wait pl/state = final]
			all [records part count = length? rows]
		]
		if empty? pl/buffer [read port]
		forever [
			complete: parse/all/case pl/buffer protocol-rules
			either all [complete not wait all [not error tail? pos]][
				clear pl/buffer
				do test-error
				break
			][
				remove/part pl/buffer (index? pos) - 1
				if any test-exit [do test-error	break]
			]
			read port
		]
		if pl/state = 'ready [pl/stream-end?: true]
	]

	protocol-rules: [
		some [ 
			pos: (stop: either any test-exit [length? pos tail pos][pos]) :stop ; exit from parser when needed
			[																	; in a Core2.5 compatible way.
				#"A" [
					read-int32 (net-log join "from " int32)
					copy msg to #"^@" (net-log pl/last-notice: msg) skip
				]
				| #"C" [
				;-- newer protocols requires reading an additional int32 here
					copy msg to #"^@" skip (
						pos: find/reverse tail pl/last-status: msg #" "
						pl/matched-rows: either pos [to integer! trim pos][0]
						pl/state: 'completed
						final: 'ready
					)
				]
				| [#"D" (sz: 4) | #"B" (sz: 0)] [
					(if decimal? fields: divide length? pl/columns 8 [fields: 1 + to integer! fields])
					copy bitmap [fields skip]
					(
						row: make block! length? pl/columns
						fields: length? trim/with sys-copy bitmap: enbase/base bitmap 2 "0"
					)
					fields [read-bytes (append row any [bytes ""])]
					(
						fields: length? pl/columns
						foreach field bitmap [
							row: either field = #"0" [sys-insert row none][next row]
							if zero? fields: fields - 1 [break]
						]
						either pl/flat? [
							sys-insert tail rows head row
						][
							sys-insert/only tail rows head row
						]
						pl/state: 'fetching-rows
					)
				]
				| #"E" [
					copy error to #"^@" skip (
						if newline = last error [remove back tail error]
						if find [auth pass-required auth-ok] pl/state [
							sys-close port/sub-port
							make error! error
						]
						final: 'ready
					)
				]
				| #"G" [
				
				]
				| #"H" [

				]
				| #"I" [
					skip (pl/state: 'empty final: 'ready)
				]
				| #"K" [
					read-int32 (pl/process-id: int32)
					read-int32 (pl/cancel-key: int32)
				]
				| #"N" [
					copy msg to #"^@" (net-log pl/last-notice: msg) skip
				]
				| #"P" [
					copy msg to #"^@" (pl/cursor: msg) skip
				]
				| #"R" [
					read-int32 a-data: (
						unsupported: func [msg][
							sys-close port/sub-port
							make error! join msg ": unsupported auth method"
						]
						switch int32 [
							0 [pl/state: 'auth-ok]
							1 [unsupported "Kerberos V4"]
							2 [unsupported "Kerberos V5"]
							3 [
								reply-password port none 
								pl/state: 'pass-required
							]
							4 [unsupported "Crypt"]
							5 [
								reply-password port sys-copy/part a-data 4
								a-data: skip a-data 4
								pl/state: 'pass-required
							]
							6 [unsupported "SCM Credential"]
						]
					) :a-data
				]
				| #"T" [
					read-int (pl/columns: make block! max int 1)
					int [
						(col: make column-class [])
						copy string to #"^@" (col/name: string) skip
						read-int32	(col/type: decode int32)
						read-int	(col/length: int)
						read-int32	(col/flags: int32)
						(append pl/columns :col)
					] (pl/state: 'fields-fetched)
				]
				| #"V" [

				]
				| #"Z" (pl/state: 'ready)
			]
		] | end
	]
	
	flush-pending-data: func [port [port!] /local pl len][
		pl: port/locals
		if not pl/stream-end? [
			net-log "flushing unread data..."
			read-stream/records/wait port [] 'ready
			net-log "flush end."
			pl/stream-end?: true
			pl/state: 'ready
		]
	]

;------ Data sending ------

	write-int32: func [value [integer!]][to string! debase/base to-hex value 16]

	write-string: func [value [string!]][head sys-insert tail sys-copy value #"^@"]

	write-lim-string: func [len [integer!] value [string!]][
		head sys-insert/dup tail sys-copy value #"^@" (len - length? value) 
	]
	
	send-packet: func [port [port!] data [string!]][
		write-io port/sub-port to binary! data length? data
		port/locals/stream-end?: false
	]
	
	insert-query: func [port [port!] data [string! block!]][
		send-packet port rejoin ["Q" data #"^@"]
		port/locals/state: 'query-sent
		read-stream/wait port 'fields-fetched
		none
	]
	
	try-reconnect: func [port [port!]][
		net-log "Connection closed by server! Reconnecting..."
		if throws/closed = catch [open port][net-error "Server down!"]
	]
	
	reply-password: func [port data /local tmp][
		data: either data [
			tmp: lowercase enbase/base checksum/method join port/pass port/user 'md5 16
			join "md5" lowercase enbase/base checksum/method join tmp data 'md5 16
		][port/pass]		
		send-packet port rejoin [
			write-int32 5 + length? data		; 4 + 1 for '\0'
			write-string data
		]
	]
	
	do-handshake: func [port [port!] /local pl client-param][
		pl: port/locals: make locals-class []
		pl/state: 'auth
		pl/buffer: make binary! pl/buf-size
		pl/conv-list: sys-copy/deep conv-model

		send-packet port rejoin [
			write-int32 296
			write-int32 131072 ; v2.0
			write-lim-string 64 port/target
			write-lim-string 32 port/user
			write-lim-string 64 ""
			write-lim-string 64 ""
			write-lim-string 64 ""
		]
		
		read-stream/wait port 'ready
		net-log "Connected to server. Handshake OK"
	]

;------ Public interface ------

    init: func [port [port!] spec /local scheme args][
        if url? spec [net-utils/url-parser/parse-url port spec]
        fast-query: either args: find port/target #"?" [
			port/target: sys-copy/part port/target args
			dehex sys-copy next args
		][none]
        scheme: port/scheme 
        port/url: spec 
        if none? port/host [
            net-error reform ["No network server for" scheme "is specified"]
        ] 
        if none? port/port-id [
            net-error reform ["No port address for" scheme "is specified"]
        ]
        if none? port/target [
		    net-error reform ["No database name for" scheme "is specified"]
        ]
        if none? port/user [port/user: make string! 0]
        if none? port/pass [port/pass: make string! 0]
        if port/pass = "?" [port/pass: ask/hide "Password: "]
    ]
    
    open: func [port [port!]][
        open-proto port   
        port/sub-port/state/flags: 524835 ; force /direct/binary mode
        do-handshake port
        port/locals/stream-end?: true	; force stream-end, so 'copy won't timeout !
        if fast-query [
        	insert port fast-query
        	fast-query: none
        ]
        port/state/tail: 10		; for 'pick to work properly
    ]
    
    close: func [port [port!]][
    	port/sub-port/timeout: 4
    	either error? try [
    		send-packet port "X"
    	][net-log "Error on closing port!"][net-log "Close ok."]
        sys-close port/sub-port
    ]
	
	insert: func [[throw] port [port!] data [string! block!] /local res][
		flush-pending-data port
		port/locals/columns: none
		
		if all [port/locals/auto-ping? data <> [ping]][
			net-log "sending ping..."
			res: catch [insert-cmd port [ping]]
			if any [res = throws/closed not res][try-reconnect port]
		]
		if throws/closed = catch [
			if all [string? data data/1 = #"["][data: load data]
			res: either block? data [
				if empty? data [net-error "No data!"]
				either string? data/1 [
					insert-query port map-rebol-values data
				][
					net-error "command dialect not yet supported"
					;insert-cmd port data
				]
			][
				insert-query port data
			]
		][net-error  "Connection lost - Port closed!"]
		res
	]
	
	pick: func [port [port!] data][
		either any [none? data data = 1][
			either port/locals/stream-end? [sys-copy []][copy/part port 1]
		][none]
	]
	
	copy: func [port /part n [integer!] /local rows][
		either not port/locals/stream-end? [
			either all [value? 'part part][
				rows: make block! n
				read-stream/records/part port rows n
			][
				rows: make block! port/locals/rows
				read-stream/records/wait port rows 'ready
				port/locals/stream-end?: true
			]
			if port/locals/auto-conv? [convert-types port rows]
			recycle
			rows
		][none]
	]
	
	set 'send-sql func [
		[throw catch]
		db [port!] data [string! block!]
		/flat /raw /named /local result pl
	][
		pl: db/locals
		pl/flat?: to logic! flat
		pl/auto-conv?: not to logic! raw
		result: any [
			insert db data
			copy db
		]
		if flat [pl/flat?: off]
		if raw  [pl/auto-conv?: on]
		either all [named block? result not empty? result][
			either flat [
				if greater? length? result length? pl/columns [
					make error! "/flat and /named not allowed in this case!"
				]
				name-fields db result
			][
				forall result [change/only result name-fields db first result]
				head result
			]
		][
			result
		]
	]

	set 'name-fields func [db [port!] record [block!] /local out cols][
		out: make block! 2 * length? record
		cols: db/locals/columns
		repeat n length? record [
			insert* tail out to word! cols/:n/name
			insert* tail out record/:n
		]
		out
	]
	
	; init 'conv-model
	extract-conv-list
	
	;--- Register ourselves. 
	net-utils/net-install pgSQL self 5432
]
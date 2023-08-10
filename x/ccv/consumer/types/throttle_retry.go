package types

import time "time"

// NewSlashRecord creates a new slash record
func NewSlashRecord(sendTime time.Time, waitingOnReply bool) (record SlashRecord) {
	return SlashRecord{
		SendTime:       sendTime,
		WaitingOnReply: true,
	}
}

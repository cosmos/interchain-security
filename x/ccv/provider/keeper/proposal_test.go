package keeper_test

//
// Initialization sub-protocol related tests of proposal.go
//

// TODO (PERMISSIONLESS)
// WE DO NOT go by order in permissionless (?) DO WE need to?
// TestGetConsumerRemovalPropsToExecute tests that pending consumer removal proposals
// that are ready to execute are accessed in order by timestamp via the iterator
//func TestGetConsumerRemovalPropsToExecute(t *testing.T) {
//	now := time.Now().UTC()
//	sampleProp1 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-2", StopTime: now}
//	sampleProp2 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-1", StopTime: now.Add(time.Hour)}
//	sampleProp3 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-4", StopTime: now.Add(-time.Hour)}
//	sampleProp4 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-3", StopTime: now}
//	sampleProp5 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-1", StopTime: now.Add(2 * time.Hour)}
//
//	getExpectedOrder := func(props []providertypes.ConsumerRemovalProposal, accessTime time.Time) []providertypes.ConsumerRemovalProposal {
//		expectedOrder := []providertypes.ConsumerRemovalProposal{}
//		for _, prop := range props {
//			if !accessTime.Before(prop.StopTime) {
//				expectedOrder = append(expectedOrder, prop)
//			}
//		}
//		// sorting by SpawnTime.UnixNano()
//		sort.Slice(expectedOrder, func(i, j int) bool {
//			if expectedOrder[i].StopTime.UTC() == expectedOrder[j].StopTime.UTC() {
//				// proposals with same StopTime
//				return expectedOrder[i].ConsumerId < expectedOrder[j].ConsumerId
//			}
//			return expectedOrder[i].StopTime.UTC().Before(expectedOrder[j].StopTime.UTC())
//		})
//		return expectedOrder
//	}
//
//	testCases := []struct {
//		propSubmitOrder []providertypes.ConsumerRemovalProposal
//		accessTime      time.Time
//	}{
//		{
//			propSubmitOrder: []providertypes.ConsumerRemovalProposal{
//				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
//			},
//			accessTime: now,
//		},
//		{
//			propSubmitOrder: []providertypes.ConsumerRemovalProposal{
//				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
//			},
//			accessTime: now.Add(time.Hour),
//		},
//		{
//			propSubmitOrder: []providertypes.ConsumerRemovalProposal{
//				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
//			},
//			accessTime: now.Add(-2 * time.Hour),
//		},
//		{
//			propSubmitOrder: []providertypes.ConsumerRemovalProposal{
//				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
//			},
//			accessTime: now.Add(3 * time.Hour),
//		},
//	}
//
//	for _, tc := range testCases {
//		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
//		defer ctrl.Finish()
//
//		expectedOrderedProps := getExpectedOrder(tc.propSubmitOrder, tc.accessTime)
//
//		for _, prop := range tc.propSubmitOrder {
//			cpProp := prop
//			providerKeeper.SetPendingConsumerRemovalProp(ctx, &cpProp)
//		}
//		propsToExecute := providerKeeper.GetConsumerRemovalPropsToExecute(ctx.WithBlockTime(tc.accessTime))
//		require.Equal(t, expectedOrderedProps, propsToExecute)
//	}
//}
